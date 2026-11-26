-- SPDX-License-Identifier: MPL-2.0
{-# OPTIONS --safe --cubical #-}
module HeapOwnershipCubical where
import HeapOwnership as H
open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe
open import Agda.Builtin.Equality
open import Agda.Builtin.Cubical.Path using (PathP)

toPath : {A : Set} {x y : A} → x ≡ y → PathP (λ _ → A) x y
toPath {x = x} refl _ = x

release-borrowed-path : ∀ bytes retained readers →
  PathP (λ _ → Maybe H.Allocation) (H.cell-step H.release (H.live bytes retained (suc readers))) nothing
release-borrowed-path bytes retained readers = toPath (H.release-borrowed-refused bytes retained readers)

release-owned-path : ∀ h addr bytes → h addr ≡ H.live bytes zero zero →
  PathP (λ _ → H.Allocation) (H.store (H.run H.release h addr) addr) H.vacant
release-owned-path h addr bytes owned = toPath (H.release-removes-owned h addr bytes owned)

span-length-path : ∀ offset count bytes → H._≤_ (offset + count) (H.length bytes) →
  PathP (λ _ → Nat) (H.length (H.borrowed-span offset count bytes)) count
span-length-path offset count bytes fits = toPath (H.span-length offset count bytes fits)
