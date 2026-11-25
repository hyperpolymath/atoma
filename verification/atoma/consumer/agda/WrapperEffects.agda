-- SPDX-License-Identifier: MPL-2.0
{-# OPTIONS --safe --without-K --cubical-compatible #-}
module WrapperEffects where
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Equality

record Registry (A : Set) : Set where
  constructor registry
  field
    rest mcp : A
    active : Bool
open Registry public

finish : {A : Set} → Registry A → Registry A
finish s = registry (rest s) (mcp s) false

-- A normal callback can modify its disjoint context. Its registry projection
-- must be unchanged; pointer validity and exclusive access are premises.
record FramedReturn {A : Set} (before : Registry A) : Set where
  constructor returned
  field
    after : Registry A
    frame : after ≡ before
open FramedReturn public

normal-return-frame : {A : Set} (r m : A) (out : FramedReturn (registry r m true)) →
  finish (after out) ≡ registry r m false
normal-return-frame r m (returned .(registry r m true) refl) = refl

invalid-span-cleanup : {A : Set} (r m : A) →
  finish (registry r m true) ≡ registry r m false
invalid-span-cleanup r m = refl

-- Explicit counterexample when a raw alias changes the other endpoint.
alias-counterexample : finish (registry false true true) ≡ registry false true false
alias-counterexample = refl

data Empty : Set where
alias-breaks-frame : finish (registry false true true) ≡ registry true true false → Empty
alias-breaks-frame ()

fold : {B : Set} → (Bool → B → Bool) → Bool → List B → Bool
fold step s [] = s
fold step s (b ∷ bs) = fold step (step s b) bs

data Checked : Set where
  invalid : Checked
  valid : Bool → Checked

scan : {B : Set} → (Bool → B → Checked) → Bool → List B → Checked
scan step s [] = valid s
scan step s (b ∷ bs) with step s b
... | invalid = invalid
... | valid next = scan step next bs

scan-refines-fold : {B : Set} (step : Bool → B → Bool)
  (foreign : Bool → B → Checked)
  (contract : ∀ s b → foreign s b ≡ valid (step s b)) →
  ∀ s bs → scan foreign s bs ≡ valid (fold step s bs)
scan-refines-fold step foreign contract s [] = refl
scan-refines-fold step foreign contract s (b ∷ bs)
  rewrite contract s b = scan-refines-fold step foreign contract (step s b) bs

-- This is an effect/loop theorem, not a claim that a machine pointer is valid.
