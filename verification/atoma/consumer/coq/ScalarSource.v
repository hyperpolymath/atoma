(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> *)
(* Independent interpretation of a closed, ASCII Zig source grammar.
   The bytes, not an emitter-supplied AST or verdict, are the proof input.
   This defines the admitted source semantics; Zig/compiler correspondence
   outside this grammar and native pointer validity are not claimed. *)
From Coq Require Import List String Ascii Arith Bool NArith.
Import ListNotations.
Open Scope string_scope.

Definition white (c : nat) := existsb (Nat.eqb c) [9; 10; 13; 32].
Definition digit (c : nat) := (48 <=? c) && (c <=? 57).
Definition letter (c : nat) :=
  ((65 <=? c) && (c <=? 90)) || ((97 <=? c) && (c <=? 122)) || (c =? 95).
Definition wordchar (c : nat) := letter c || digit c.

Fixpoint take_word (xs : list nat) : string * list nat :=
  match xs with
  | [] => (EmptyString, [])
  | c :: rest => if wordchar c then
      let '(s, tail) := take_word rest in (String (ascii_of_nat c) s, tail)
    else (EmptyString, xs)
  end.

Fixpoint after_comment (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | c :: rest => if c =? 10 then rest else after_comment rest
  end.

(* Fuel decreases on every token, whitespace byte or line comment. *)
Fixpoint lex (fuel : nat) (xs : list nat) : option (list string) :=
  match xs with
  | [] => Some []
  | c :: rest =>
    match fuel with
    | 0 => None
    | S fuel' =>
      if white c then lex fuel' rest else
      if c =? 47 then
        match rest with
        | 47 :: tail => lex fuel' (after_comment tail)
        | _ => None
        end
      else
        let token_tail :=
          if wordchar c then Some (take_word xs) else
          match xs with
          | 62 :: 61 :: tail => Some (">=", tail)
          | 60 :: 61 :: tail => Some ("<=", tail)
          | 60 :: 60 :: tail => Some ("<<", tail)
          | _ => if existsb (Nat.eqb c) [40; 41; 58; 123; 125; 59; 64; 44; 124]
                 then Some (String (ascii_of_nat c) EmptyString, rest)
                 else None
          end in
        match token_tail with
        | None => None
        | Some (t, tail) =>
          match lex fuel' tail with
          | Some ts => Some (t :: ts)
          | None => None
          end
        end
    end
  end.

Fixpoint decimal_acc (s : string) (acc : nat) : option nat :=
  match s with
  | EmptyString => Some acc
  | String c rest =>
    let n := nat_of_ascii c in
    if digit n then decimal_acc rest (10 * acc + (n - 48)) else None
  end.
Definition decimal (s : string) : option nat :=
  (* A small, explicit literal grammar; no hex, suffixes or coercions. *)
  if (1 <=? String.length s) && (String.length s <=? 3)
  then decimal_acc s 0 else None.

Fixpoint identifier_tail (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest => wordchar (nat_of_ascii c) && identifier_tail rest
  end.
Definition identifier (s : string) : bool :=
  let reserved := ["pub"; "fn"; "return"; "u8"; "u64"; "bool";
                   "and"; "or"; "as"; "true"; "false"; "undefined"; "_"] in
  match s with
  | EmptyString => false
  | String c rest => letter (nat_of_ascii c) && identifier_tail rest &&
                     negb (existsb (String.eqb s) reserved)
  end.

Inductive expression :=
| shift_or (shift tag : nat)
| inclusive_range (lo hi : nat).

Definition parse_tokens (ts : list string) : option expression :=
  match ts with
  | ["pub"; "fn"; f; "("; x; ":"; "u8"; ")"; "u64"; "{";
     "return"; "("; "@"; "as"; "("; "u64"; ","; y; ")";
     "<<"; shift; ")"; "|"; tag; ";"; "}"] =>
    if identifier f && identifier x && negb (String.eqb f x) && String.eqb x y
    then match decimal shift, decimal tag with
         | Some s, Some t => if (s <=? 56) && (t <=? 255)
                             then Some (shift_or s t) else None
         | _, _ => None
         end
    else None
  | ["pub"; "fn"; f; "("; x; ":"; "u8"; ")"; "bool"; "{";
     "return"; y; ">="; lo; "and"; z; "<="; hi; ";"; "}"] =>
    if identifier f && identifier x && negb (String.eqb f x) &&
       String.eqb x y && String.eqb x z
    then match decimal lo, decimal hi with
         | Some l, Some h => if (l <=? 255) && (h <=? 255)
                             then Some (inclusive_range l h) else None
         | _, _ => None
         end
    else None
  | _ => None
  end.

Definition parse (bytes : list nat) : option expression :=
  if forallb (fun c => c <? 128) bytes then
    match lex (List.length bytes) bytes with
    | Some ts => parse_tokens ts
    | None => None
    end
  else None.

Definition evaluate (e : expression) (x : nat) : N :=
  match e with
  | shift_or shift tag => N.lor (N.shiftl (N.of_nat x) (N.of_nat shift)) (N.of_nat tag)
  | inclusive_range lo hi => if (lo <=? x) && (x <=? hi) then 1%N else 0%N
  end.
Definition run (bytes : list nat) (x : nat) : option N :=
  match parse bytes with Some e => Some (evaluate e x) | None => None end.
Definition accepts (bytes : list nat) : bool :=
  match parse bytes with Some _ => true | None => false end.
Definition check (bytes : list nat) (expected : list N) : bool :=
  match parse bytes with
  | None => false
  | Some e => (List.length expected =? 256) &&
      forallb (fun x => N.eqb (evaluate e x) (nth x expected 0%N) &&
                       N.ltb (evaluate e x) (N.pow 2 64)) (seq 0 256)
  end.

Theorem check_sound : forall bytes expected,
  check bytes expected = true -> forall x, x < 256 ->
  run bytes x = Some (nth x expected 0%N).
Proof.
  intros bytes expected H x Hx.
  unfold check in H. unfold run.
  destruct (parse bytes) as [e|] eqn:E; [|discriminate].
  apply andb_true_iff in H as [_ H].
  rewrite forallb_forall in H.
  assert (Hin : In x (seq 0 256)).
  { apply in_seq. split; [apply Nat.le_0_l | exact Hx]. }
  specialize (H x Hin). apply andb_true_iff in H as [H _].
  apply N.eqb_eq in H. now rewrite H.
Qed.

Theorem check_range : forall bytes expected,
  check bytes expected = true -> forall x, x < 256 ->
  exists result, run bytes x = Some result /\ (result < N.pow 2 64)%N.
Proof.
  intros bytes expected H x Hx.
  unfold check in H. unfold run.
  destruct (parse bytes) as [e|] eqn:E; [|discriminate].
  apply andb_true_iff in H as [_ H]. rewrite forallb_forall in H.
  assert (Hin : In x (seq 0 256)).
  { apply in_seq. split; [apply Nat.le_0_l | exact Hx]. }
  specialize (H x Hin). apply andb_true_iff in H as [_ H].
  exists (evaluate e x). split; [reflexivity | now apply N.ltb_lt].
Qed.
Print Assumptions check_sound.
Print Assumptions check_range.
