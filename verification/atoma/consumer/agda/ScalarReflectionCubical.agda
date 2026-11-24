-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
{-# OPTIONS --safe --cubical --double-check #-}
module ScalarReflectionCubical where
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Cubical.Path using (PathP)
open import ScalarReflection

toPath : ∀ {A : Set} {x y : A} → x ≡ y → PathP (λ _ → A) x y
toPath {x = x} refl i = x

reflection-path : {A : Set} (eq : A → A → Bool) →
  ((a b : A) → eq a b ≡ true → a ≡ b) →
  ∀ n (body contract : Fin n → A) →
  allFin n (λ i → eq (body i) (contract i)) ≡ true →
  (i : Fin n) → PathP (λ _ → A) (body i) (contract i)
reflection-path eq eq-sound n body contract checked i =
  toPath (reflection-sound eq eq-sound n body contract checked i)
