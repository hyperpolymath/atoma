(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> *)
(* Closed guarded-decoder source semantics. Original bytes and the complete
   imported encoder are inputs; an emitter-supplied AST/verdict is not used.
   Machine/compiler and pointer-carrier correspondence are separate. *)
From Coq Require Import List String Ascii Bool NArith PeanoNat Nnat Lia.
Require Import ScalarSource CanonicalWord.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

Fixpoint strip_prefix (prefix xs : list nat) : option (list nat) :=
  match prefix, xs with
  | [], _ => Some xs
  | p :: ps, x :: rest => if Nat.eqb p x then strip_prefix ps rest else None
  | _, _ => None
  end.

(* Only this literal import is admitted, including its unbroken quoted bytes.
   Ignoring whitespace/comments inside string literals would be unsound. *)
Definition import_literal : list nat :=
  [34;98;105;116;115;56;95;119;111;114;100;46;122;105;103;34].

Fixpoint lex (fuel : nat) (xs : list nat) : option (list string) :=
  match xs with
  | [] => Some []
  | c :: rest => match fuel with
    | O => None
    | S fuel' =>
      if ScalarSource.white c then lex fuel' rest else
      match xs with
      | 47 :: 47 :: tail => lex fuel' (ScalarSource.after_comment tail)
      | _ =>
        let token_tail :=
          if Nat.eqb c 34 then
            match strip_prefix import_literal xs with
            | Some tail => Some ("encoder-import", tail) | None => None end
          else if ScalarSource.wordchar c then Some (ScalarSource.take_word xs)
          else match xs with
          | 33 :: 61 :: tail => Some ("!=", tail)
          | _ => if existsb (Nat.eqb c) [40;41;58;123;125;59;64;44;61;33;46;47;62]
                 then Some (String (ascii_of_nat c) EmptyString, rest)
                 else None
          end in
        match token_tail with
        | None => None
        | Some (t, tail) => match lex fuel' tail with
          | Some ts => Some (t :: ts) | None => None end
        end
      end
    end
  end.

Fixpoint decimal_acc (s : string) (acc : N) : option N :=
  match s with
  | EmptyString => Some acc
  | String c rest => let n := nat_of_ascii c in
      if ScalarSource.digit n
      then decimal_acc rest (10 * acc + N.of_nat (n - 48))%N else None
  end.
Definition decimal (s : string) : option N :=
  if Nat.leb 1 (String.length s) && Nat.leb (String.length s) 20
  then decimal_acc s 0%N else None.

Record program := Program { divisor : N; maximum : N }.

(* This is one deliberately closed straight-line grammar: unsigned division,
   refusal before checked narrowing, a bound import call, equality refusal,
   and return. All names, types, order and trailing declarations are checked.
   Literals become operands in the operational interpretation below. *)
Definition parse_tokens (ts : list string) : option program :=
  match ts with
  | ["const";"word";"=";"@";"import";"(";"encoder-import";")";";";
     "pub";"fn";"decodeWord";"(";"raw";":";"u64";")";
     "error";"{";"InvalidRefcResult";"}";"!";"u8";"{";
     "const";"payload";"=";"raw";"/";d;";";
     "if";"(";"payload";">";m;")";"return";"error";".";"InvalidRefcResult";";";
     "const";"byte";":";"u8";"=";"@";"intCast";"(";"payload";")";";";
     "if";"(";"raw";"!=";"word";".";"encodeWord";"(";"byte";")";")";
     "return";"error";".";"InvalidRefcResult";";";
     "return";"byte";";";"}"] =>
       match decimal d, decimal m with
       | Some divisor, Some maximum => Some (Program divisor maximum)
       | _, _ => None end
  | _ => None
  end.
Definition parse (bytes : list nat) : option program :=
  if forallb (fun c => Nat.ltb c 128) bytes then
    match lex (List.length bytes) bytes with
    | Some ts => parse_tokens ts | None => None end
  else None.

Definition encoder_export (bytes : list nat) : bool :=
  match ScalarSource.lex (List.length bytes) bytes with
  | Some ("pub" :: "fn" :: "encodeWord" :: _) => true
  | _ => false end.
Definition encoder_row (bytes : list nat) (b : nat) : bool :=
  match ScalarSource.run bytes b with
  | Some value => N.eqb value (CanonicalWord.encode (N.of_nat b))
  | None => false end.
Definition encoder_check (bytes : list nat) : bool :=
  encoder_export bytes && forallb (encoder_row bytes) (seq 0 256).

Lemma encoder_check_sound : forall bytes,
  encoder_check bytes = true -> forall b, (b < 256)%N ->
  ScalarSource.run bytes (N.to_nat b) = Some (CanonicalWord.encode b).
Proof.
  intros bytes H b Hb. unfold encoder_check in H.
  apply andb_true_iff in H as [_ H]. rewrite forallb_forall in H.
  assert (Hn : (N.to_nat b < 256)%nat).
  { apply Nat.compare_lt_iff.
    change ((N.to_nat b ?= N.to_nat 256)%nat = Lt).
    rewrite <- N2Nat.inj_compare. exact Hb. }
  assert (Hin : In (N.to_nat b) (seq 0 256)).
  { apply in_seq. split; [lia | exact Hn]. }
  specialize (H (N.to_nat b) Hin). unfold encoder_row in H.
  destruct (ScalarSource.run bytes (N.to_nat b)) as [v|] eqn:E; [|discriminate].
  apply N.eqb_eq in H. rewrite N2Nat.id in H. now rewrite H.
Qed.

Definition check (source encoder : list nat) : bool :=
  match parse source with
  | Some p => N.eqb (divisor p) CanonicalWord.stride &&
      (N.eqb (maximum p) 255 && encoder_check encoder)
  | None => false end.

(* A checked u8 cast preserves b only in range. The refusal precedes that cast.
   The actual parsed encoder is evaluated at the narrowed byte. *)
(* Outer None denotes unsupported evaluation or a trap, never a normal
   InvalidRefcResult. The correspondence theorem excludes it universally. *)
Definition evaluate (p : program) (encoder : list nat) (w : N) : option (option N) :=
  if N.eqb (divisor p) 0 then None else
  let b := (w / divisor p)%N in
  if (b <=? maximum p)%N then
    if (b <? 256)%N then
      match ScalarSource.run encoder (N.to_nat b) with
      | Some canonical => Some (if N.eqb w canonical then Some b else None)
      | None => None end
    else None
  else Some None.
Definition run (source encoder : list nat) (w : N) : option (option N) :=
  match parse source with Some p => evaluate p encoder w | None => None end.

Theorem source_corresponds : forall source encoder,
  check source encoder = true -> forall w,
  run source encoder w = Some (CanonicalWord.decode w).
Proof.
  intros source encoder H w. unfold check in H. unfold run.
  destruct (parse source) as [[d m]|] eqn:E; [|discriminate].
  apply andb_true_iff in H as [Hd H]. apply andb_true_iff in H as [Hm He].
  cbn in Hd, Hm. apply N.eqb_eq in Hd. apply N.eqb_eq in Hm. subst d m.
  unfold evaluate, CanonicalWord.decode, CanonicalWord.payload. cbn [divisor maximum].
  change ((if (w / CanonicalWord.stride <=? 255)%N then
    if (w / CanonicalWord.stride <? 256)%N then
      match ScalarSource.run encoder (N.to_nat (w / CanonicalWord.stride)) with
      | Some canonical => Some (if N.eqb w canonical then Some (w / CanonicalWord.stride)%N else None)
      | None => None end
    else None else Some None) =
    Some (if (w / CanonicalWord.stride <? 256)%N then
      if (w =? CanonicalWord.encode (w / CanonicalWord.stride))%N then Some (w / CanonicalWord.stride)%N else None
      else None)).
  remember (w / CanonicalWord.stride)%N as b.
  destruct (b <? 256)%N eqn:Hb.
  - apply N.ltb_lt in Hb.
    assert (Hle : (b <=? 255)%N = true) by (apply N.leb_le; lia).
    rewrite Hle, (encoder_check_sound encoder He b Hb). reflexivity.
  - apply N.ltb_ge in Hb.
    assert (Hle : (b <=? 255)%N = false) by (apply N.leb_gt; lia).
    now rewrite Hle.
Qed.

Theorem source_exact : forall source encoder,
  check source encoder = true -> forall w b,
  run source encoder w = Some (Some b) <-> (b < 256)%N /\ w = CanonicalWord.encode b.
Proof.
  intros source encoder H w b. rewrite (source_corresponds source encoder H w).
  split.
  - intro E. injection E as E. now apply CanonicalWord.decode_exact.
  - intro E. now rewrite (proj2 (CanonicalWord.decode_exact w b) E).
Qed.

Print Assumptions encoder_check_sound.
Print Assumptions source_corresponds.
Print Assumptions source_exact.
