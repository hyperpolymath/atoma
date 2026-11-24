-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
{-# OPTIONS --safe --without-K --cubical-compatible --double-check #-}
module ScalarReflection where
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

data Fin : Nat → Set where
  first : ∀ {n} → Fin (suc n)
  next : ∀ {n} → Fin n → Fin (suc n)

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

allFin : (n : Nat) → (Fin n → Bool) → Bool
allFin zero p = true
allFin (suc n) p = p first && allFin n (λ i → p (next i))

left : ∀ {a b} → (a && b) ≡ true → a ≡ true
left {true} h = refl
left {false} ()

right : ∀ {a b} → (a && b) ≡ true → b ≡ true
right {true} h = h
right {false} ()

allFin-sound : (n : Nat) (p : Fin n → Bool) →
  allFin n p ≡ true → (i : Fin n) → p i ≡ true
allFin-sound zero p h ()
allFin-sound (suc n) p h first = left h
allFin-sound (suc n) p h (next i) =
  allFin-sound n (λ j → p (next j)) (right {a = p first} h) i

-- A successful exhaustive check establishes equality for every inhabitant,
-- provided the equality test reflects equality. It does not certify a parser.
reflection-sound : {A : Set} (eq : A → A → Bool) →
  ((a b : A) → eq a b ≡ true → a ≡ b) →
  (n : Nat) (body contract : Fin n → A) →
  allFin n (λ i → eq (body i) (contract i)) ≡ true →
  (i : Fin n) → body i ≡ contract i
reflection-sound eq eq-sound n body contract checked i =
  eq-sound (body i) (contract i)
    (allFin-sound n (λ j → eq (body j) (contract j)) checked i)
