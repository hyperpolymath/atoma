(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> *)
From Coq Require Import List String Ascii Bool Arith ZArith Lia.
Require Import ScalarSource.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.
Open Scope list_scope.

(* Closed lexical/profile grammar: generic opaque endpoint values, records,
   field selection, copy/update, branches, local calls and signed status guards.
   No imports, pointers, loops, effects or arbitrary comptime evaluation. *)
Fixpoint lex (fuel : nat) (xs : list nat) : option (list string) :=
  match xs with
  | [] => Some []
  | c :: rest => match fuel with
    | O => None
    | S fuel' => if ScalarSource.white c then lex fuel' rest else
      match xs with
      | 47 :: 47 :: tail => lex fuel' (ScalarSource.after_comment tail)
      | _ => let token_tail :=
        if ScalarSource.wordchar c then Some (ScalarSource.take_word xs) else
        match xs with
        | 61 :: 62 :: tail => Some ("=>", tail)
        | 61 :: 61 :: tail => Some ("==", tail)
        | 33 :: 61 :: tail => Some ("!=", tail)
        | 62 :: 61 :: tail => Some (">=", tail)
        | 60 :: 61 :: tail => Some ("<=", tail)
        | _ => if existsb (Nat.eqb c) [40;41;58;123;125;59;64;44;61;63;46]
               then Some (String (ascii_of_nat c) EmptyString, rest) else None
        end in
        match token_tail with
        | Some (t, tail) => match lex fuel' tail with Some ts => Some (t::ts) | None => None end
        | None => None end
      end
    end
  end.
Fixpoint strip (prefix xs : list string) : option (list string) :=
  match prefix, xs with
  | [], _ => Some xs
  | p::ps, x::rest => if String.eqb p x then strip ps rest else None
  | _, _ => None end.
Definition same (a b : list string) : bool :=
  if list_eq_dec string_dec a b then true else false.
Fixpoint body (fuel depth : nat) (acc xs : list string) : option (list string * list string) :=
  match fuel, xs with
  | S f, "}"::rest => match depth with
      | O => Some (rev acc, rest) | S d => body f d ("}"::acc) rest end
  | S f, "{"::rest => body f (S depth) ("{"::acc) rest
  | S f, x::rest => body f depth (x::acc) rest
  | _, _ => None end.
Fixpoint functions (sigs : list (list string)) (xs : list string) : option (list (list string)) :=
  match sigs with
  | [] => if same xs [] then Some [] else None
  | sig::rest => match strip sig xs with
    | Some tail => match body (List.length tail) 0 [] tail with
      | Some (b, tail') => match functions rest tail' with Some bs => Some (b::bs) | None => None end
      | None => None end
    | None => None end
  end.

Definition generic := ["comptime";"E";":";"type"].
Definition signatures : list (list string) :=
 [ ["pub";"fn";"State";"("] ++ generic ++ [")";"type";"{"];
   ["pub";"fn";"Reply";"("] ++ generic ++ [")";"type";"{"];
   ["pub";"fn";"get";"("] ++ generic ++ [",";"s";":";"State";"(";"E";")";",";"slot";":";"Slot";")";"?";"E";"{"];
   ["pub";"fn";"put";"("] ++ generic ++ [",";"s";":";"State";"(";"E";")";",";"slot";":";"Slot";",";"endpoint";":";"?";"E";")";"State";"(";"E";")";"{"];
   ["pub";"fn";"mark";"("] ++ generic ++ [",";"s";":";"State";"(";"E";")";",";"active";":";"bool";")";"State";"(";"E";")";"{"];
   ["pub";"fn";"register";"("] ++ generic ++ [",";"s";":";"State";"(";"E";")";",";"slot";":";"Slot";",";"endpoint";":";"E";")";"Reply";"(";"E";")";"{"];
   ["pub";"fn";"unregister";"("] ++ generic ++ [",";"s";":";"State";"(";"E";")";",";"slot";":";"Slot";")";"Reply";"(";"E";")";"{"];
   ["pub";"fn";"begin";"("] ++ generic ++ [",";"s";":";"State";"(";"E";")";",";"slot";":";"Slot";")";"Reply";"(";"E";")";"{"];
   ["pub";"fn";"finish";"("] ++ generic ++ [",";"s";":";"State";"(";"E";")";")";"State";"(";"E";")";"{"];
   ["pub";"fn";"sanitize";"(";"status";":";"c_int";")";"c_int";"{"] ].

Inductive field := RestField | McpField.
Inductive value := FromRest | FromMcp | Argument.
Definition parse_field (s : string) : option field :=
  match s with "rest" => Some RestField | "mcp" => Some McpField | _ => None end.
Definition parse_value (xs : list string) : option (value * list string) :=
  match xs with
  | "s"::"."::"rest"::rest => Some (FromRest, rest)
  | "s"::"."::"mcp"::rest => Some (FromMcp, rest)
  | "endpoint"::rest => Some (Argument, rest)
  | _ => None end.
Definition parse_record (xs : list string) : option ((value * value) * list string) :=
  match strip [".";"{";".";"rest";"="] xs with
  | Some tail => match parse_value tail with
    | Some (r, ","::"."::"mcp"::"="::tail') => match parse_value tail' with
      | Some (m, ","::"."::"active"::"="::"s"::"."::"active"::"}"::rest) => Some ((r,m),rest)
      | _ => None end
    | _ => None end
  | None => None end.
Definition parse_get (xs : list string) : option (field * field) :=
  match xs with
  | ["return";"switch";"(";"slot";")";"{";".";"mcp";"=>";"s";".";m;",";".";"rest";"=>";"s";".";r;"}";";"] =>
      match parse_field m, parse_field r with Some a, Some b => Some (a,b) | _,_ => None end
  | _ => None end.
Definition parse_put (xs : list string) : option ((value * value) * (value * value)) :=
  match strip ["return";"switch";"(";"slot";")";"{";".";"mcp";"=>"] xs with
  | Some tail => match parse_record tail with
    | Some (a, ","::"."::"rest"::"=>"::tail') => match parse_record tail' with
      | Some (b, [",";"}";";"]) => Some (a,b) | _ => None end
    | _ => None end
  | None => None end.
Definition parse_mark (xs : list string) : option (field * field) :=
  match xs with
  | ["return";".";"{";".";"rest";"=";"s";".";r;",";".";"mcp";"=";"s";".";m;",";".";"active";"=";"active";"}";";"] =>
      match parse_field r, parse_field m with Some a,Some b => Some (a,b) | _,_ => None end
  | _ => None end.
Definition numbers (a b c : string) : option (nat * nat * nat) :=
  match ScalarSource.decimal a, ScalarSource.decimal b, ScalarSource.decimal c with
  | Some x,Some y,Some z => Some (x,y,z) | _,_,_ => None end.
Definition parse_update (comparison argument : string) (xs : list string) : option (nat * nat * nat) :=
  match xs with
  | ["if";"(";"s";".";"active";")";"return";".";"{";".";"status";"=";busy;",";".";"next";"=";"s";"}";";";
     "if";"(";"get";"(";"E";",";"s";",";"slot";")";cmp;"null";")";"return";".";"{";".";"status";"=";other;",";".";"next";"=";"s";"}";";";
     "return";".";"{";".";"status";"=";ok;",";".";"next";"=";"put";"(";"E";",";"s";",";"slot";",";arg;")";"}";";"] =>
       if String.eqb cmp comparison && String.eqb arg argument then numbers busy other ok else None
  | _ => None end.
Definition parse_begin (xs : list string) : option (nat * nat * nat) :=
  match xs with
  | ["if";"(";"s";".";"active";")";"return";".";"{";".";"status";"=";busy;",";".";"next";"=";"s";"}";";";
     "const";"endpoint";"=";"get";"(";"E";",";"s";",";"slot";")";"orelse";"return";".";"{";".";"status";"=";absent;",";".";"next";"=";"s";"}";";";
     "return";".";"{";".";"status";"=";ok;",";".";"next";"=";"mark";"(";"E";",";"s";",";"true";")";",";".";"selected";"=";"endpoint";"}";";"] => numbers busy absent ok
  | _ => None end.
Definition parse_finish (xs : list string) : option bool :=
  match xs with
  | ["return";"mark";"(";"E";",";"s";",";"false";")";";"] => Some false
  | ["return";"mark";"(";"E";",";"s";",";"true";")";";"] => Some true
  | _ => None end.
Definition parse_sanitize (xs : list string) : option (nat * nat * nat) :=
  match xs with
  | ["return";"if";"(";"status";">=";lo;"and";"status";"<=";hi;")";"status";"else";fallback;";"] => numbers lo hi fallback
  | _ => None end.

Record program := Program {
  selectors : field * field;
  updates : (value * value) * (value * value);
  marked_fields : field * field;
  register_codes : nat * nat * nat;
  unregister_codes : nat * nat * nat;
  begin_codes : nat * nat * nat;
  finish_flag : bool;
  status_bounds : nat * nat * nat
}.
Definition parse_bodies (bs : list (list string)) : option program :=
  match bs with
  | [st;rp;g;p;m;r;u;b;f;z] =>
    if same st ["return";"struct";"{";"rest";":";"?";"E";"=";"null";",";"mcp";":";"?";"E";"=";"null";",";"active";":";"bool";"=";"false";"}";";"] &&
       same rp ["return";"struct";"{";"status";":";"u8";",";"next";":";"State";"(";"E";")";",";"selected";":";"?";"E";"=";"null";"}";";"] then
    match parse_get g, parse_put p, parse_mark m, parse_update "!=" "endpoint" r,
          parse_update "==" "null" u, parse_begin b, parse_finish f, parse_sanitize z with
    | Some gp,Some pp,Some mp,Some rp,Some up,Some bp,Some fp,Some zp => Some (Program gp pp mp rp up bp fp zp)
    | _,_,_,_,_,_,_,_ => None end else None
  | _ => None end.
Definition parse (bytes : list nat) : option program :=
  if forallb (fun c => Nat.ltb c 128) bytes then
  match lex (List.length bytes) bytes with
  | Some ts => match strip ["pub";"const";"Slot";"=";"enum";"{";"mcp";",";"rest";"}";";"] ts with
    | Some tail => match functions signatures tail with Some bs => parse_bodies bs | None => None end
    | None => None end
  | None => None end else None.

Inductive slot := MCP | REST.
Record state (A : Type) := State { rest : option A; mcp : option A; active : bool }.
Arguments State {A}. Arguments rest {A}. Arguments mcp {A}. Arguments active {A}.
Record reply (A : Type) := Reply { status : nat; next : state A; selected : option A }.
Arguments Reply {A}. Arguments status {A}. Arguments next {A}. Arguments selected {A}.
Definition field_value {A} (f : field) (s : state A) := match f with RestField => rest s | McpField => mcp s end.
Definition expression {A} (e : value) (s : state A) (argument : option A) :=
  match e with FromRest => rest s | FromMcp => mcp s | Argument => argument end.
Definition get {A} (p : program) (s : state A) (k : slot) :=
  field_value (match k with MCP => fst (selectors p) | REST => snd (selectors p) end) s.
Definition put {A} (p : program) (s : state A) (k : slot) (e : option A) :=
  let pair := match k with MCP => fst (updates p) | REST => snd (updates p) end in
  State (expression (fst pair) s e) (expression (snd pair) s e) (active s).
Definition mark {A} (p : program) (s : state A) (b : bool) :=
  State (field_value (fst (marked_fields p)) s) (field_value (snd (marked_fields p)) s) b.
Definition register {A} (p : program) (s : state A) (k : slot) (e : A) :=
  let '(busy,duplicate,ok) := register_codes p in
  if active s then Reply busy s None else match get p s k with
  | Some _ => Reply duplicate s None | None => Reply ok (put p s k (Some e)) None end.
Definition unregister {A} (p : program) (s : state A) (k : slot) :=
  let '(busy,absent,ok) := unregister_codes p in
  if active s then Reply busy s None else match get p s k with
  | None => Reply absent s None | Some _ => Reply ok (put p s k None) None end.
Definition begin {A} (p : program) (s : state A) (k : slot) :=
  let '(busy,absent,ok) := begin_codes p in
  if active s then Reply busy s None else match get p s k with
  | None => Reply absent s None | Some e => Reply ok (mark p s true) (Some e) end.
Definition finish {A} (p : program) (s : state A) := mark p s (finish_flag p).
Definition sanitize (p : program) (z : Z) : Z :=
  let '(lo,hi,fallback) := status_bounds p in
  if (Z.of_nat lo <=? z)%Z && (z <=? Z.of_nat hi)%Z then z else Z.of_nat fallback.

Definition canonical := Program (McpField,RestField)
  ((FromRest,Argument),(Argument,FromMcp)) (RestField,McpField)
  (6,9,0) (6,8,0) (6,11,0) false (0,11,6).
Definition program_eq_dec (a b : program) : {a=b}+{a<>b}.
Proof. repeat decide equality. Defined.
Definition check (bytes : list nat) : bool := match parse bytes with
  | Some p => if program_eq_dec p canonical then true else false | None => false end.
Lemma check_binds : forall bytes, check bytes = true -> parse bytes = Some canonical.
Proof.
  intros bytes H. unfold check in H. destruct (parse bytes) as [p|] eqn:E; [|discriminate].
  destruct (program_eq_dec p canonical); [now subst | discriminate].
Qed.

(* Independent contract denotation corresponding to Abi.RegistryState.
   Source parsing/evaluation above supplies field identities and operation codes. *)
Definition lookup {A} (s : state A) (k : slot) := match k with MCP => mcp s | REST => rest s end.
Definition replace {A} (s : state A) (k : slot) (e : option A) := match k with
  | MCP => State (rest s) e (active s) | REST => State e (mcp s) (active s) end.
Definition busy_state {A} (s : state A) (b : bool) := State (rest s) (mcp s) b.
Definition spec_register {A} (s : state A) (k : slot) (e : A) :=
  if active s then Reply 6 s None else match lookup s k with
  | Some _ => Reply 9 s None | None => Reply 0 (replace s k (Some e)) None end.
Definition spec_unregister {A} (s : state A) (k : slot) :=
  if active s then Reply 6 s None else match lookup s k with
  | None => Reply 8 s None | Some _ => Reply 0 (replace s k None) None end.
Definition spec_begin {A} (s : state A) (k : slot) :=
  if active s then Reply 6 s None else match lookup s k with
  | None => Reply 11 s None | Some e => Reply 0 (busy_state s true) (Some e) end.

Theorem source_refines : forall bytes,
  check bytes = true -> exists p, parse bytes = Some p /\
  (forall A (s : state A) k e, register p s k e = spec_register s k e) /\
  (forall A (s : state A) k, unregister p s k = spec_unregister s k) /\
  (forall A (s : state A) k, begin p s k = spec_begin s k) /\
  (forall A (s : state A), finish p s = busy_state s false) /\
  (forall z, sanitize p z = if (0 <=? z)%Z && (z <=? 11)%Z then z else 6%Z).
Proof.
  intros bytes H. exists canonical. repeat split.
  - now apply check_binds.
  - intros A s k e. destruct k; reflexivity.
  - intros A s k. destruct k; reflexivity.
  - intros A s k. destruct k; reflexivity.
Qed.

Definition other (k : slot) := match k with MCP => REST | REST => MCP end.
Theorem update_frames_other : forall A (s : state A) k e,
  lookup (replace s k e) (other k) = lookup s (other k).
Proof. intros A s k e. destruct k; reflexivity. Qed.
Theorem begin_identity : forall A (s : state A) k e,
  active s = false -> lookup s k = Some e ->
  spec_begin s k = Reply 0 (busy_state s true) (Some e).
Proof. intros A s k e Hb He. unfold spec_begin. now rewrite Hb, He. Qed.
Theorem reentrant_refused : forall A (s : state A) k,
  spec_begin (busy_state s true) k = Reply 6 (busy_state s true) None.
Proof. reflexivity. Qed.
Theorem normal_return_frames : forall A (s : state A),
  rest (finish canonical s) = rest s /\ mcp (finish canonical s) = mcp s /\ active (finish canonical s) = false.
Proof. intros. repeat split; reflexivity. Qed.
Theorem foreign_status_bounded : forall z, (0 <= sanitize canonical z <= 11)%Z.
Proof.
  intro z. change (0 <= (if (0 <=? z)%Z && (z <=? 11)%Z then z else 6) <= 11)%Z.
  destruct ((0 <=? z)%Z && (z <=? 11)%Z) eqn:E.
  - apply andb_true_iff in E as [L H]. apply Z.leb_le in L. apply Z.leb_le in H. lia.
  - lia.
Qed.
Print Assumptions source_refines.
Print Assumptions update_frames_other.
Print Assumptions begin_identity.
Print Assumptions reentrant_refused.
Print Assumptions normal_return_frames.
Print Assumptions foreign_status_bounded.
