(* SPDX-License-Identifier: MPL-2.0 *)
(* Closed original public-entry interpretation. Pointer/region correspondence,
   machine representability and compiler correctness remain premises. *)
From Coq Require Import List String Ascii Bool Arith ZArith Lia.
Require Import ScalarSource RegistrySource WrapperSource HeapOwnership HeaderBoundaryContext.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.
Open Scope list_scope.

Fixpoint same_bytes (a b : list nat) : bool :=
  match a,b with
  | [],[] => true
  | x::xs,y::ys => Nat.eqb x y && same_bytes xs ys
  | _,_ => false end.
Definition peel (prefix suffix bytes : list nat) : option (list nat) :=
  let pre := List.length prefix in let post := List.length suffix in
  let size := List.length bytes in
  if (pre + post <=? size) && same_bytes prefix (firstn pre bytes) &&
     same_bytes suffix (skipn (size-post) bytes)
  then Some (firstn (size-pre-post) (skipn pre bytes)) else None.

(* Same restricted ASCII tokens as WrapperSource, with the '-' token needed by
   the actual public status mapping. Minus is not erased or substituted. *)
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
          match WrapperSource.literal (List.length rest) rest with
          | Some (s,tail) => Some (String.append "quoted:" s,tail) | None => None end
          else if ScalarSource.wordchar c then Some (ScalarSource.take_word xs)
          else match xs with
          | 61::61::tail => Some ("==",tail)
          | 33::61::tail => Some ("!=",tail)
          | 61::62::tail => Some ("=>",tail)
          | _ => if existsb (Nat.eqb c) [40;41;58;123;125;59;64;44;45;61;63;46;42;33;91;93;124;62]
                 then Some (String (ascii_of_nat c) EmptyString,rest) else None end in
        match token with
        | Some (t,tail) => match lex f tail with Some ts => Some (t::ts) | None => None end
        | None => None end
      end
    end end.
Definition tokenize bytes := if forallb (fun c => c <? 128) bytes
  then lex (List.length bytes) bytes else None.

Record program := Program { slice_start : nat; unavailable_error : nat; invalid_error : nat }.
Definition canonical := Program 0 99 7.
Definition parse_body ts :=
  match WrapperSource.operands
    [["const";"p";"=";"ptr";"orelse";"return";"BoolResult";"{";".";"status";"=";"PROVEN_ERR_NULL_POINTER";",";".";"value";"=";"false";"}";";";
      "const";"detected";"=";"header_backend";".";"detect";"(";"p";"["];
     [".";".";"len";"]";")";"catch";"|";"err";"|";"{";"setError";"(";"quoted:Header backend failure";")";";";
      "return";".";"{";".";"status";"=";"if";"(";"@";"as";"(";"anyerror";",";"err";")";"==";"error";".";"BackendUnavailable";")";"-"];
     ["else";"-"];
     [",";".";"value";"=";"false";"}";";";"}";";";
      "return";".";"{";".";"status";"=";"PROVEN_OK";",";".";"value";"=";"detected";"}";";"]] ts with
  | Some [start;missing;invalid] => Some (Program start missing invalid)
  | _ => None end.
Definition parse_core bytes :=
  match peel HeaderBoundaryContext.core_prefix HeaderBoundaryContext.core_suffix bytes with
  | Some body => match tokenize body with Some ts => parse_body ts | None => None end
  | None => None end.
Definition check_export bytes :=
  match peel HeaderBoundaryContext.export_prefix HeaderBoundaryContext.export_suffix bytes with
  | Some body => match tokenize body with
    | Some ts => RegistrySource.same ts ["return";"core";".";"headerHasCrlf";"(";"@";"import";"(";"quoted:header_refc.zig";")";",";"ptr";",";"len";")";";"]
    | None => false end
  | None => false end.
Definition program_eq_dec (a b : program) : {a=b}+{a<>b}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition check core exports := match parse_core core with
  | Some p => if program_eq_dec p canonical then check_export exports else false
  | None => false end.
Lemma bound : forall core exports, check core exports = true ->
  parse_core core = Some canonical /\ check_export exports = true.
Proof.
  intros core exports H; unfold check in H.
  destruct (parse_core core) as [p|] eqn:E; [|discriminate].
  destruct (program_eq_dec p canonical); [subst; auto|discriminate].
Qed.

Inductive backend_outcome := BackendValue (value : bool) | BackendMissing | BackendInvalid.
Definition backend_fn := list nat -> HeapOwnership.heap -> bool ->
  (HeapOwnership.heap * bool) * backend_outcome.
Record observation := Observe {
  status : Z; value : bool; final_heap : HeapOwnership.heap;
  error_mark : bool; calls : list (list nat)
}.
(* error_mark is only a projection of thread-local error presence/effects, not
   the native error pointer or a theorem about message storage layout. *)
Definition finish_call p result after tls bytes := match result with
  | BackendValue b => Observe 0%Z b after tls [bytes]
  | BackendMissing => Observe (- Z.of_nat (unavailable_error p))%Z false after true [bytes]
  | BackendInvalid => Observe (- Z.of_nat (invalid_error p))%Z false after true [bytes]
  end.
(* None means the request lies outside the admitted readable-span interpretation;
   it is NOT an additional runtime refusal implemented by core.zig. A native
   pointer and its usize range must correspond to this live region and snapshot.
   The physical read lease must stay valid and immutable throughout the call;
   a backend may not retain the span. Final heap equality cannot establish that
   temporal condition: a native backend could write and restore between reads. *)
Definition run p (present : bool) (h : HeapOwnership.heap) addr offset count tls
  (backend : backend_fn) :=
  if present then
    match h addr with
    | HeapOwnership.Vacant => None
    | HeapOwnership.Live bytes retained readers =>
      if HeapOwnership.span_fits offset count bytes then
        let span := skipn (slice_start p) (HeapOwnership.borrowed_span offset count bytes) in
        let '((after,after_tls),result) := backend span h tls in
        Some (finish_call p result after after_tls span)
      else None
    end
  else Some (Observe (-1)%Z false h tls []).
Definition backend_frames (addr : nat)
  (backend : backend_fn) := forall span h tls,
  fst (fst (backend span h tls)) addr = h addr.
(* backend_frames states FINAL region equality only. It does not imply a
   continuous no-write/no-retention discipline for an arbitrary foreign call. *)

Theorem source_null : forall core exports h addr offset count tls backend,
  check core exports = true -> exists p,
  parse_core core = Some p /\ check_export exports = true /\
  run p false h addr offset count tls backend = Some (Observe (-1)%Z false h tls []).
Proof. intros; destruct (bound core exports H) as [Hp He].
  exists canonical; repeat split; auto. Qed.

Theorem source_normal : forall core exports h addr offset count tls backend bytes retained readers,
  check core exports = true -> h addr = HeapOwnership.Live bytes retained (S readers) ->
  HeapOwnership.span_fits offset count bytes = true -> backend_frames addr backend ->
  exists p, parse_core core = Some p /\ check_export exports = true /\
  exists observed, run p true h addr offset count tls backend = Some observed /\
    calls observed = [HeapOwnership.borrowed_span offset count bytes] /\
    final_heap observed addr = h addr /\
    HeapOwnership.cell_step HeapOwnership.ReturnRead (final_heap observed addr) =
      Some (HeapOwnership.Live bytes retained readers).
Proof.
  intros core exports h addr offset count tls backend bytes retained readers Hsource Hcell Hfits Hframe.
  destruct (bound core exports Hsource) as [Hp He].
  exists canonical; split; [exact Hp|]; split; [exact He|].
  unfold run; rewrite Hcell, Hfits; simpl.
  pose proof (Hframe (HeapOwnership.borrowed_span offset count bytes) h tls) as Hsame.
  destruct (backend (HeapOwnership.borrowed_span offset count bytes) h tls) as [[after after_tls] result] eqn:E.
  simpl in Hsame. exists (finish_call canonical result after after_tls (HeapOwnership.borrowed_span offset count bytes)).
  split; [reflexivity|]. destruct result; simpl; repeat split;
    try reflexivity; try exact Hsame; rewrite Hsame, Hcell; reflexivity.
Qed.

Theorem result_mapping : forall result after tls span,
  status (finish_call canonical result after tls span) =
    match result with BackendValue _ => 0%Z | BackendMissing => (-99)%Z | BackendInvalid => (-7)%Z end /\
  value (finish_call canonical result after tls span) =
    match result with BackendValue b => b | _ => false end /\
  error_mark (finish_call canonical result after tls span) =
    match result with BackendValue _ => tls | _ => true end.
Proof. intros; destruct result; repeat split; reflexivity. Qed.

Definition implements_scan foreign
  (backend : backend_fn) := forall span h tls,
  snd (backend span h tls) = match WrapperSource.header_run WrapperSource.header_canonical foreign span with
    | Some b => BackendValue b | None => BackendInvalid end.
Definition interpreted_backend foreign
  (effect : list nat -> HeapOwnership.heap -> bool -> HeapOwnership.heap * bool)
  (span : list nat) (h : HeapOwnership.heap) (tls : bool) :=
  (effect span h tls, match WrapperSource.header_run WrapperSource.header_canonical foreign span with
    | Some b => BackendValue b | None => BackendInvalid end).
(* This composes the checked callee's snapshot semantics. Relating native reads
   to that snapshot still requires the synchronous immutable read-lease premise;
   the arbitrary effect parameter is not certified to obey that premise. *)
Theorem source_fold : forall core exports header h addr offset count tls backend bytes retained readers step foreign,
  check core exports = true -> WrapperSource.check_header header = true ->
  h addr = HeapOwnership.Live bytes retained (S readers) ->
  HeapOwnership.span_fits offset count bytes = true ->
  Forall (fun b => b < 256) (HeapOwnership.borrowed_span offset count bytes) ->
  (forall s b, b < 256 -> foreign (WrapperSource.encode s) b = Some (WrapperSource.encode (step s b))) ->
  implements_scan foreign backend ->
  exists p, parse_core core = Some p /\ check_export exports = true /\
  exists observed, run p true h addr offset count tls backend = Some observed /\
    status observed = 0%Z /\ value observed =
      WrapperSource.fold step false (HeapOwnership.borrowed_span offset count bytes).
Proof.
  intros core exports header h addr offset count tls backend bytes retained readers step foreign
    Hsource Hheader Hcell Hfits Hbytes Hforeign Hbackend.
  destruct (bound core exports Hsource) as [Hp He].
  destruct (WrapperSource.header_source_fold header step foreign
    (HeapOwnership.borrowed_span offset count bytes) Hheader Hbytes Hforeign) as [scan [Hscan Hfold]].
  rewrite (WrapperSource.header_bound header Hheader) in Hscan; inversion Hscan; subst scan.
  pose proof (Hbackend (HeapOwnership.borrowed_span offset count bytes) h tls) as Hout.
  rewrite Hfold in Hout.
  exists canonical; split; [exact Hp|]; split; [exact He|].
  unfold run; rewrite Hcell, Hfits; simpl.
  destruct (backend (HeapOwnership.borrowed_span offset count bytes) h tls) as [[after after_tls] result] eqn:E.
  simpl in Hout; subst result.
  eexists; repeat split; reflexivity.
Qed.

(* Dropping the frame premise is observably unsound: a foreign backend can
   return a heap in which the borrowed region was destroyed. This is not a pass
   for native memory safety; it records the necessary contract boundary. *)
Example unframed_backend_counterexample :
  let h : HeapOwnership.heap := fun _ => HeapOwnership.Live [13] 0 1 in
  let bad := fun (_ : list nat) (_ : HeapOwnership.heap) (_ : bool) =>
    (((fun _ => HeapOwnership.Vacant),false),BackendValue false) in
  exists observed, run canonical true h 0 0 1 false bad = Some observed /\
    final_heap observed 0 <> h 0.
Proof. simpl; eexists; split; [reflexivity|discriminate]. Qed.

Print Assumptions source_null.
Print Assumptions source_normal.
Print Assumptions result_mapping.
Print Assumptions source_fold.
Print Assumptions unframed_backend_counterexample.
