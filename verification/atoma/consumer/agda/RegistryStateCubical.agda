-- SPDX-License-Identifier: MPL-2.0
{-# OPTIONS --safe --cubical #-}
module RegistryStateCubical where
open import Agda.Builtin.Cubical.Path using (PathP)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe
open import RegistryState
to-path : {A : Set} {x y : A} → x ≡ y → PathP (λ _ → A) x y
to-path {x = x} refl i = x
update-frame-path : {A : Set} (k : Slot) (e : Maybe A) (s : State A) →
  PathP (λ _ → Maybe A) (lookup (other k) (put k e s)) (lookup (other k) s)
update-frame-path k e s = to-path (update-frame k e s)
identity-path : {A : Set} (k : Slot) (r m : Maybe A) (e : A) →
  lookup k (state r m false) ≡ just e →
  PathP (λ _ → Result A) (begin k (state r m false)) (called e (state r m true))
identity-path k r m e found = to-path (begin-identity k r m e found)
reentrant-path : {A : Set} (k : Slot) (s : State A) →
  PathP (λ _ → Result A) (begin k (mark s true)) (refused (mark s true))
reentrant-path k s = to-path (reentrant-refused k s)
return-path : {A : Set} (k : Slot) (s : State A) →
  PathP (λ _ → Maybe A) (lookup k (mark s false)) (lookup k s)
return-path k s = to-path (normal-return-frame k s)

