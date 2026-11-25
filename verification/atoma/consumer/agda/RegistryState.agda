-- SPDX-License-Identifier: MPL-2.0
{-# OPTIONS --safe --without-K --cubical-compatible #-}
module RegistryState where
open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe
open import Agda.Builtin.Equality

data Slot : Set where rest-slot mcp-slot : Slot
record State (A : Set) : Set where
  constructor state
  field rest mcp : Maybe A
        active : Bool
open State public
lookup : {A : Set} → Slot → State A → Maybe A
lookup rest-slot s = rest s
lookup mcp-slot s = mcp s
other : Slot → Slot
other rest-slot = mcp-slot
other mcp-slot = rest-slot
put : {A : Set} → Slot → Maybe A → State A → State A
put rest-slot e s = state e (mcp s) (active s)
put mcp-slot e s = state (rest s) e (active s)
mark : {A : Set} → State A → Bool → State A
mark s b = state (rest s) (mcp s) b
data Result (A : Set) : Set where
  refused : State A → Result A
  called : A → State A → Result A
begin : {A : Set} → Slot → State A → Result A
begin k s@(state r m true) = refused s
begin k s@(state r m false) with lookup k s
... | nothing = refused s
... | just e = called e (mark s true)

update-frame : {A : Set} (k : Slot) (e : Maybe A) (s : State A) →
  lookup (other k) (put k e s) ≡ lookup (other k) s
update-frame rest-slot e s = refl
update-frame mcp-slot e s = refl
update-identity : {A : Set} (k : Slot) (e : Maybe A) (s : State A) →
  lookup k (put k e s) ≡ e
update-identity rest-slot e s = refl
update-identity mcp-slot e s = refl
begin-identity : {A : Set} (k : Slot) (r m : Maybe A) (e : A) →
  lookup k (state r m false) ≡ just e →
  begin k (state r m false) ≡ called e (state r m true)
begin-identity k r m e found rewrite found = refl
reentrant-refused : {A : Set} (k : Slot) (s : State A) →
  begin k (mark s true) ≡ refused (mark s true)
reentrant-refused k s = refl
normal-return-frame : {A : Set} (k : Slot) (s : State A) →
  lookup k (mark s false) ≡ lookup k s
normal-return-frame rest-slot s = refl
normal-return-frame mcp-slot s = refl
normal-return-idle : {A : Set} (s : State A) → active (mark s false) ≡ false
normal-return-idle s = refl

