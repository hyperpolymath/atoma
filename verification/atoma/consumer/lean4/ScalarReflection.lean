-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-- Re-proof of finite reflection. No Mathlib; not a Zig parser theorem.
def allBefore : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allBefore n p && p n

theorem allBefore_sound (n : Nat) (p : Nat → Bool)
    (h : allBefore n p = true) : ∀ i, i < n → p i = true := by
  induction n with
  | zero => intro i hi; exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
    have parts : allBefore n p = true ∧ p n = true := by
      simpa only [allBefore, Bool.and_eq_true] using h
    intro i hi
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with he | hl
    · simpa [he] using parts.2
    · exact ih parts.1 i hl

theorem reflection_sound {A : Type} (eq : A → A → Bool)
    (eq_sound : ∀ a b, eq a b = true → a = b)
    (n : Nat) (body contract : Nat → A)
    (checked : allBefore n (fun i => eq (body i) (contract i)) = true) :
    ∀ i, i < n → body i = contract i := by
  intro i hi
  exact eq_sound _ _ (allBefore_sound n _ checked i hi)

#print axioms allBefore_sound
#print axioms reflection_sound
