(* SPDX-License-Identifier: MPL-2.0 *)
(* Original-byte closed wrapper grammar. No claimed full Zig parser/compiler refinement. *)
From Coq Require Import List String Ascii Bool Arith ZArith Lia.
Require Import ScalarSource RegistrySource.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.
Open Scope list_scope.

Fixpoint literal (fuel : nat) (xs : list nat) : option (string * list nat) :=
 match fuel, xs with
 | S f, 34::rest => Some (EmptyString,rest)
 | S f, c::rest =>
   if (32 <=? c) && (c <? 127) && negb (Nat.eqb c 92) then
   match literal f rest with Some (s,tail) => Some (String (ascii_of_nat c) s,tail) | None => None end
   else None
 | _,_ => None end.
Fixpoint lex (fuel : nat) (xs : list nat) : option (list string) :=
 match xs with
 | [] => Some []
 | c::rest => match fuel with
 | O => None
 | S f => if ScalarSource.white c then lex f rest else
   match xs with
   | 47::47::tail => lex f (ScalarSource.after_comment tail)
   | _ =>
     let token := if Nat.eqb c 34 then
       match literal (List.length rest) rest with
       | Some (s,tail) => Some ("quoted:" ++ s,tail) | None => None end
       else if ScalarSource.wordchar c then Some (ScalarSource.take_word xs)
       else match xs with
       | 61::61::tail => Some ("==",tail)
       | 33::61::tail => Some ("!=",tail)
       | 61::62::tail => Some ("=>",tail)
       | _ => if existsb (Nat.eqb c) [40;41;58;123;125;59;64;44;61;63;46;42;33;91;93;124;62]
              then Some (String (ascii_of_nat c) EmptyString,rest) else None end in
     match token with
     | Some (t,tail) => match lex f tail with Some ts => Some (t::ts) | None => None end
     | None => None end
   end
 end end.
Definition tokenize (bytes : list nat) :=
 if forallb (fun c => Nat.ltb c 128) bytes then lex (List.length bytes) bytes else None.

Record registry_program := CallProgram {
 null_code : nat; busy_code : nat; tag_code : nat;
 unsupported_code : nat; selected_code : nat; span_code : nat }.
Definition registry_canonical := CallProgram 4 6 2 11 11 4.
Definition parse_call (ts : list string) : option registry_program :=
 match ts with
 | ["const";"registry";"=";"r";"orelse";"return";null_code;";";"if";"(";"registry";".";"active";")";"return";busy_code;";";"if";"(";"!";"known";"(";"tag";")";")";"return";tag_code;";";"const";"slot";":";"state";".";"Slot";"=";"switch";"(";"tag";")";"{";"1";"=>";".";"mcp";",";"9";"=>";".";"rest";",";"else";"=>";"return";unsupported_code;",";"}";";";"const";"reply";"=";"state";".";"begin";"(";"Endpoint";",";"registry";".";"*";",";"slot";")";";";"if";"(";"reply";".";"status";"!=";"0";")";"return";"reply";".";"status";";";"const";"endpoint";"=";"reply";".";"selected";"orelse";"return";selected_code;";";"registry";".";"*";"=";"reply";".";"next";";";"defer";"registry";".";"*";"=";"state";".";"finish";"(";"Endpoint";",";"registry";".";"*";")";";";"if";"(";"bytes";"==";"null";"and";"len";"!=";"0";")";"return";span_code;";";"const";"status";"=";"endpoint";".";"callback";"(";"endpoint";".";"context";",";"bytes";",";"len";")";";";"return";"state";".";"sanitize";"(";"status";")";";"] =>
   match ScalarSource.decimal null_code, ScalarSource.decimal busy_code,
         ScalarSource.decimal tag_code, ScalarSource.decimal unsupported_code,
         ScalarSource.decimal selected_code, ScalarSource.decimal span_code with
   | Some a,Some b,Some c,Some d,Some e,Some f => Some (CallProgram a b c d e f)
   | _,_,_,_,_,_ => None end
 | _ => None end.
(* Imported names, callback ABI and surrounding declarations are closed.
   Create/destroy/register/unregister are scoped as checked source closure,
   not additional ownership/refinement theorems. *)
Definition registry_prefix := ["const";"std";"=";"@";"import";"(";"quoted:std";")";";";"const";"known";"=";"@";"import";"(";"quoted:protocol_tag.zig";")";".";"known";";";"const";"state";"=";"@";"import";"(";"quoted:registry_state.zig";")";";";"pub";"const";"Callback";"=";"*";"const";"fn";"(";"?";"*";"anyopaque";",";"?";"[";"*";"]";"const";"u8";",";"usize";")";"callconv";"(";".";"c";")";"c_int";";";"const";"Endpoint";"=";"struct";"{";"callback";":";"Callback";",";"context";":";"?";"*";"anyopaque";"}";";";"pub";"const";"Registry";"=";"state";".";"State";"(";"Endpoint";")";";"].
Definition registry_signatures := [["pub";"export";"fn";"uaa_registry_create";"(";")";"?";"*";"Registry";"{"];
["pub";"export";"fn";"uaa_registry_destroy";"(";"r";":";"?";"*";"Registry";")";"c_int";"{"];
["pub";"export";"fn";"uaa_registry_register";"(";"r";":";"?";"*";"Registry";",";"tag";":";"u8";",";"callback";":";"?";"Callback";",";"context";":";"?";"*";"anyopaque";")";"c_int";"{"];
["pub";"export";"fn";"uaa_registry_unregister";"(";"r";":";"?";"*";"Registry";",";"tag";":";"u8";")";"c_int";"{"];
["pub";"export";"fn";"uaa_registry_call";"(";"r";":";"?";"*";"Registry";",";"tag";":";"u8";",";"bytes";":";"?";"[";"*";"]";"const";"u8";",";"len";":";"usize";")";"c_int";"{"]].
Definition parse_registry (bytes : list nat) : option registry_program :=
 match tokenize bytes with
 | Some ts => match RegistrySource.strip registry_prefix ts with
   | Some tail => match RegistrySource.functions registry_signatures tail with
     | Some [create;destroy;register;unregister;call] =>
       if RegistrySource.same create ["const";"r";"=";"std";".";"heap";".";"c_allocator";".";"create";"(";"Registry";")";"catch";"return";"null";";";"r";".";"*";"=";".";"{";"}";";";"return";"r";";"] &&
          RegistrySource.same destroy ["const";"registry";"=";"r";"orelse";"return";"4";";";"if";"(";"registry";".";"active";")";"return";"6";";";"std";".";"heap";".";"c_allocator";".";"destroy";"(";"registry";")";";";"return";"0";";"] &&
          RegistrySource.same register ["const";"registry";"=";"r";"orelse";"return";"4";";";"if";"(";"registry";".";"active";")";"return";"6";";";"if";"(";"!";"known";"(";"tag";")";")";"return";"2";";";"const";"slot";":";"state";".";"Slot";"=";"switch";"(";"tag";")";"{";"1";"=>";".";"mcp";",";"9";"=>";".";"rest";",";"else";"=>";"return";"11";",";"}";";";"const";"cb";"=";"callback";"orelse";"return";"4";";";"const";"reply";"=";"state";".";"register";"(";"Endpoint";",";"registry";".";"*";",";"slot";",";".";"{";".";"callback";"=";"cb";",";".";"context";"=";"context";"}";")";";";"registry";".";"*";"=";"reply";".";"next";";";"return";"reply";".";"status";";"] &&
          RegistrySource.same unregister ["const";"registry";"=";"r";"orelse";"return";"4";";";"if";"(";"registry";".";"active";")";"return";"6";";";"if";"(";"!";"known";"(";"tag";")";")";"return";"2";";";"const";"slot";":";"state";".";"Slot";"=";"switch";"(";"tag";")";"{";"1";"=>";".";"mcp";",";"9";"=>";".";"rest";",";"else";"=>";"return";"11";",";"}";";";"const";"reply";"=";"state";".";"unregister";"(";"Endpoint";",";"registry";".";"*";",";"slot";")";";";"registry";".";"*";"=";"reply";".";"next";";";"return";"reply";".";"status";";"]
       then parse_call call else None
     | _ => None end
   | None => None end
 | None => None end.

Record header_program := HeaderProgram { initial_state : nat; maximum_state : nat; final_state : nat }.
Definition header_canonical := HeaderProgram 0 1 1.
Definition parse_scan (ts : list string) : option header_program :=
 match ts with
 | [final] =>
   match ScalarSource.decimal initial,ScalarSource.decimal maximum,ScalarSource.decimal final with
   | Some i,Some m,Some f => Some (HeaderProgram i m f) | _,_,_ => None end
 | _ => None end.
Definition parse_header (bytes : list nat) : option header_program :=
 match tokenize bytes with
 | Some ts => match RegistrySource.strip ["const";"bits8";"=";"@";"import";"(";"quoted:refc/bits8.zig";")";";";"extern";"fn";"Proven_SafeHeader_ByteKernel_headerStep";"(";"?";"*";"anyopaque";",";"?";"*";"anyopaque";")";"callconv";"(";".";"c";")";"?";"*";"anyopaque";";";"extern";"fn";"idris2_trampoline";"(";"?";"*";"anyopaque";")";"callconv";"(";".";"c";")";"?";"*";"anyopaque";";";"pub";"fn";"detect";"(";"bytes";":";"[";"]";"const";"u8";")";"error";"{"] ts with
   | Some tail => match RegistrySource.body (List.length tail) 0 [] tail with
     | Some (b,rest) => if RegistrySource.same rest ["!";"bool";"{";"var";"state";":";"u8";"=";"0";";";"for";"(";"bytes";")";"|";"b";"|";"{";"const";"result";"=";"idris2_trampoline";"(";"Proven_SafeHeader_ByteKernel_headerStep";"(";"bits8";".";"encode";"(";"state";")";",";"bits8";".";"encode";"(";"b";")";")";")";";";"const";"next";"=";"try";"bits8";".";"decode";"(";"result";")";";";"if";"(";"next";">";"1";")";"return";"error";".";"InvalidRefcResult";";";"state";"=";"next";";";"}";"return";"state";"==";"1";";";"}";"test";"{";"_";"=";"bits8";";";"}"] then parse_scan b else None
     | None => None end
   | None => None end
 | None => None end.
Definition registry_eq_dec (a b : registry_program) : {a=b}+{a<>b}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition header_eq_dec (a b : header_program) : {a=b}+{a<>b}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition check_registry bytes := match parse_registry bytes with
 | Some p => if registry_eq_dec p registry_canonical then true else false | None => false end.
Definition check_header bytes := match parse_header bytes with
 | Some p => if header_eq_dec p header_canonical then true else false | None => false end.
Lemma registry_bound : forall bytes, check_registry bytes = true -> parse_registry bytes = Some registry_canonical.
Proof. intros bytes H. unfold check_registry in H. destruct (parse_registry bytes) as [p|] eqn:E; [|discriminate].
 destruct (registry_eq_dec p registry_canonical); [now subst|discriminate]. Qed.
Lemma header_bound : forall bytes, check_header bytes = true -> parse_header bytes = Some header_canonical.
Proof. intros bytes H. unfold check_header in H. destruct (parse_header bytes) as [p|] eqn:E; [|discriminate].
 destruct (header_eq_dec p header_canonical); [now subst|discriminate]. Qed.

(* A heap projection: this record is the registry allocation. The callback's
   disjoint context may change freely; this projection must be preserved.
   A live readable allocation and serialized access are external premises. *)
Definition observation A := (Z * RegistrySource.state A * option A)%type.
Definition outcome {A} (code : nat) (s : RegistrySource.state A) : observation A :=
  (Z.of_nat code,s,None).
Definition invoke {A} (p : registry_program) (s : RegistrySource.state A)
  (slot : RegistrySource.slot) (span_valid : bool)
  (callback : A -> RegistrySource.state A -> RegistrySource.state A * Z) : observation A :=
  let reply := RegistrySource.begin RegistrySource.canonical s slot in
  if negb (Nat.eqb (RegistrySource.status reply) 0) then outcome (RegistrySource.status reply) s else
  match RegistrySource.selected reply with
  | None => outcome (selected_code p) s
  | Some endpoint =>
    let borrowed := RegistrySource.next reply in
    if span_valid then
      let '(after,code) := callback endpoint borrowed in
      (RegistrySource.sanitize RegistrySource.canonical code,
       RegistrySource.finish RegistrySource.canonical after,Some endpoint)
    else outcome (span_code p) (RegistrySource.finish RegistrySource.canonical borrowed)
  end.
Definition registry_run {A} (p : registry_program) (present : bool)
  (s : RegistrySource.state A) (tag : nat) (span_valid : bool) callback : observation A :=
  if negb present then outcome (null_code p) s else
  if RegistrySource.active s then outcome (busy_code p) s else
  if negb ((1 <=? tag) && (tag <=? 9)) then outcome (tag_code p) s else
  match tag with
  | 1 => invoke p s RegistrySource.MCP span_valid callback
  | 9 => invoke p s RegistrySource.REST span_valid callback
  | _ => outcome (unsupported_code p) s end.
Definition final_registry {A} (out : observation A) := snd (fst out).
Definition callback_frames {A} (callback : A -> RegistrySource.state A -> RegistrySource.state A * Z) := forall (e : A) s,
  fst (callback e s) = s.

Lemma invoke_frames : forall A p (s : RegistrySource.state A) k valid callback,
  RegistrySource.active s = false -> callback_frames callback ->
  final_registry (invoke p s k valid callback) = s.
Proof.
  intros A p [r m busy] k valid callback Hb Hframe. simpl in Hb. subst busy.
  destruct k; unfold invoke, RegistrySource.begin, RegistrySource.get,
    RegistrySource.canonical, RegistrySource.field_value; simpl;
    destruct m as [em|]; try destruct r as [er|]; simpl;
    try reflexivity;
    destruct valid; simpl; try reflexivity;
    match goal with
    | |- context [callback ?e ?s] => specialize (Hframe e s);
      destruct (callback e s) as [after code] eqn:E; simpl in Hframe; subst after
    end; reflexivity.
Qed.
Theorem registry_normal_frame : forall bytes A present (s : RegistrySource.state A) tag valid callback,
  check_registry bytes = true -> RegistrySource.active s = false ->
  callback_frames callback ->
  exists p, parse_registry bytes = Some p /\
    final_registry (registry_run p present s tag valid callback) = s.
Proof.
  intros bytes A present s tag valid callback Hsource Hidle Hframe.
  exists registry_canonical. split; [now apply registry_bound|].
  unfold registry_run. rewrite Hidle. destruct present; simpl; [|reflexivity].
  destruct ((1 <=? tag) && (tag <=? 9)); simpl; [|reflexivity].
  do 10 (destruct tag as [|tag]; try reflexivity; try (now apply invoke_frames)).
  reflexivity.
Qed.
Theorem busy_refuses : forall A p (s : RegistrySource.state A) tag valid callback,
  RegistrySource.active s = true ->
  registry_run p true s tag valid callback = outcome (busy_code p) s.
Proof. intros. unfold registry_run. simpl. now rewrite H. Qed.
Theorem no_callback_for_invalid_span : forall A p (s : RegistrySource.state A) k callback,
  snd (invoke p s k false callback) = None.
Proof.
  intros. unfold invoke. destruct (negb (Nat.eqb (RegistrySource.status (RegistrySource.begin RegistrySource.canonical s k)) 0)); [reflexivity|].
  destruct (RegistrySource.selected (RegistrySource.begin RegistrySource.canonical s k)); reflexivity.
Qed.
Example raw_alias_counterexample :
  final_registry (registry_run registry_canonical true
    (RegistrySource.State (Some 9) (Some 1) false) 1 true
    (fun _ _ => (RegistrySource.State None (Some 1) true,7%Z))) =
  RegistrySource.State None (Some 1) false.
Proof. reflexivity. Qed.

(* Each loop iteration reads one element of the borrowed immutable list. The
   foreign step has no heap authority here; that is an ASSUMED external call
   contract, not a conclusion about arbitrary native code or the compiler. *)
Fixpoint scan (p : header_program) (step : nat -> nat -> option nat)
  (state : nat) (bytes : list nat) : option nat :=
  match bytes with
  | [] => Some state
  | b::bs => match step state b with
    | Some next => if next <=? maximum_state p then scan p step next bs else None
    | None => None end
  end.
Definition header_run p step bytes :=
  match scan p step (initial_state p) bytes with
  | Some state => Some (Nat.eqb state (final_state p)) | None => None end.
Definition encode (s : bool) : nat := if s then 1 else 0.
Fixpoint fold (step : bool -> nat -> bool) (s : bool) (bytes : list nat) : bool :=
  match bytes with [] => s | b::bs => fold step (step s b) bs end.
Lemma scan_fold : forall (step : bool -> nat -> bool) foreign,
  (forall s b, foreign (encode s) b = Some (encode (step s b))) ->
  forall bs s, scan header_canonical foreign (encode s) bs = Some (encode (fold step s bs)).
Proof.
  intros step foreign H bs. induction bs as [|b bs IH]; intro s; [reflexivity|].
  simpl. rewrite H. destruct (step s b) eqn:E; simpl; apply IH.
Qed.
Theorem header_source_fold : forall bytes step foreign bs,
  check_header bytes = true ->
  (forall s b, foreign (encode s) b = Some (encode (step s b))) ->
  exists p, parse_header bytes = Some p /\
    header_run p foreign bs = Some (fold step false bs).
Proof.
  intros bytes step foreign bs Hsource Hcall. exists header_canonical.
  split; [now apply header_bound|]. unfold header_run.
  change (match scan header_canonical foreign (encode false) bs with
    | Some state => Some (Nat.eqb state 1) | None => None end = Some (fold step false bs)).
  rewrite (scan_fold step foreign Hcall). destruct (fold step false bs); reflexivity.
Qed.
Fixpoint read_count (p : header_program) (step : nat -> nat -> option nat)
  (state : nat) (bytes : list nat) : nat := match bytes with
 | [] => 0
 | b::bs => S (match step state b with
   | Some next => if next <=? maximum_state p then read_count p step next bs else 0
   | None => 0 end) end.
Theorem bounded_reads : forall p step bs s, read_count p step s bs <= List.length bs.
Proof.
 intros p step bs. induction bs as [|b bs IH]; intro s; simpl; [lia|].
 destruct (step s b) as [next|]; [destruct (next <=? maximum_state p)|]; simpl; try lia.
 specialize (IH next). lia.
Qed.
Print Assumptions registry_normal_frame.
Print Assumptions busy_refuses.
Print Assumptions no_callback_for_invalid_span.
Print Assumptions raw_alias_counterexample.
Print Assumptions header_source_fold.
Print Assumptions bounded_reads.
