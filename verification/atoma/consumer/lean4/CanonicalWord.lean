-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
import Std.Tactic

namespace CanonicalWord
def stride : Nat := 4294967296
def encode (b : Nat) : Nat := b * stride + 1
def payload (w : Nat) : Nat := w / stride
def decode (w : Nat) : Option Nat :=
  if payload w < 256 then
    if w = encode (payload w) then some (payload w) else none
  else none

theorem payload_encode (b : Nat) : payload (encode b) = b := by
  unfold payload encode stride
  omega

theorem decode_exact (w b : Nat) :
    decode w = some b ↔ b < 256 ∧ w = encode b := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · rename_i bound
      split at h
      · rename_i same
        have hb := Option.some.inj h
        exact ⟨hb ▸ bound, hb ▸ same⟩
      · cases h
    · cases h
  · rintro ⟨bound, rfl⟩
    unfold decode
    rw [payload_encode]
    rw [if_pos bound, if_pos rfl]

theorem noncanonical_refused (w : Nat)
    (h : ∀ b, b < 256 → w ≠ encode b) : decode w = none := by
  cases result : decode w with
  | none => rfl
  | some b =>
    have parts := (decode_exact w b).mp result
    exact False.elim (h b parts.1 parts.2)

theorem encode_injective (a b : Nat) (h : encode a = encode b) : a = b := by
  have hp := congrArg payload h
  rw [payload_encode, payload_encode] at hp
  exact hp

theorem canonical_word_range (b : Nat) (h : b < 256) :
    0 < encode b ∧ encode b < 18446744073709551616 := by
  unfold encode stride
  omega

#print axioms decode_exact
#print axioms noncanonical_refused
#print axioms encode_injective
#print axioms canonical_word_range
end CanonicalWord
