(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> *)
(* Arithmetic model over ALL natural words, hence also all uint64 inputs.
   Relating the bit-field Agda model and the source interpreter is separate. *)
From Coq Require Import NArith Lia.
Open Scope N_scope.

Definition stride : N := 4294967296.
Definition encode (b : N) : N := b * stride + 1.
Definition payload (w : N) : N := w / stride.
Definition decode (w : N) : option N :=
  let b := payload w in
  if b <? 256 then
    if w =? encode b then Some b else None
  else None.

Lemma payload_encode : forall b, payload (encode b) = b.
Proof.
  intro b. unfold payload, encode.
  rewrite N.div_add_l by (unfold stride; discriminate).
  assert (H : 1 / stride = 0) by (apply N.div_small; unfold stride; reflexivity).
  rewrite H. apply N.add_0_r.
Qed.

Theorem decode_exact : forall w b,
  decode w = Some b <-> b < 256 /\ w = encode b.
Proof.
  intros w b. split.
  - unfold decode. destruct (payload w <? 256) eqn:Hbound; [|discriminate].
    destruct (w =? encode (payload w)) eqn:Hword; [|discriminate].
    intro H. inversion H; subst. split.
    + now apply N.ltb_lt.
    + now apply N.eqb_eq.
  - intros [Hbound ->]. unfold decode. rewrite payload_encode.
    apply N.ltb_lt in Hbound. rewrite Hbound, N.eqb_refl. reflexivity.
Qed.

Theorem noncanonical_refused : forall w,
  (forall b, b < 256 -> w <> encode b) -> decode w = None.
Proof.
  intros w H. destruct (decode w) as [b|] eqn:E; [|reflexivity].
  apply decode_exact in E as [Hb Ew]. exfalso. exact (H b Hb Ew).
Qed.

Theorem encode_injective : forall a b, encode a = encode b -> a = b.
Proof.
  intros a b H. apply (f_equal payload) in H.
  now rewrite !payload_encode in H.
Qed.

Theorem canonical_word_range : forall b, b < 256 ->
  0 < encode b < 18446744073709551616.
Proof. intros b Hb. unfold encode, stride. nia. Qed.

Print Assumptions decode_exact.
Print Assumptions noncanonical_refused.
Print Assumptions encode_injective.
Print Assumptions canonical_word_range.
