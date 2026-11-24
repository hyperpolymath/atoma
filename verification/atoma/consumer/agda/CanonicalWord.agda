-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
{-# OPTIONS --safe --without-K --cubical-compatible --double-check #-}
module CanonicalWord where
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Equality using (_≡_; refl)

data Empty : Set where

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

Bits : Nat → Set
Bits zero = ⊤
Bits (suc n) = Σ Bool (λ _ → Bits n)

zeros : (n : Nat) → Bits n
zeros zero = tt
zeros (suc n) = false , zeros n

allZero : (n : Nat) → Bits n → Bool
allZero zero tt = true
allZero (suc n) (false , tail) = allZero n tail
allZero (suc n) (true , tail) = false

allZero-sound : (n : Nat) (xs : Bits n) →
  allZero n xs ≡ true → xs ≡ zeros n
allZero-sound zero tt h = refl
allZero-sound (suc n) (false , xs) h =
  cong (λ tail → false , tail) (allZero-sound n xs h)
allZero-sound (suc n) (true , xs) ()

-- Every 64-bit pattern has these fields: 24 + 8 + 31 + 1 bits.
-- No enumeration or assumption that the input was produced by encode.
record Word : Set where
  constructor word
  field
    high : Bits 24
    payload : Bits 8
    padding : Bits 31
    tag : Bool
open Word

encode : Bits 8 → Word
encode b = word (zeros 24) b (zeros 31) true

decode : Word → Maybe (Bits 8)
decode (word h b l false) = nothing
decode (word h b l true) with allZero 24 h | allZero 31 l
... | true | true = just b
... | true | false = nothing
... | false | _ = nothing

just-injective : {A : Set} {a b : A} → just a ≡ just b → a ≡ b
just-injective refl = refl

impossible : {A B : Set} {b : A} → nothing ≡ just b → B
impossible ()

decode-sound : (w : Word) (b : Bits 8) →
  decode w ≡ just b → w ≡ encode b
decode-sound (word h p l false) b ()
decode-sound (word h p l true) b eq
  with allZero 24 h in eh | allZero 31 l in el
... | true | true
  rewrite allZero-sound 24 h eh | allZero-sound 31 l el
        | just-injective eq = refl
... | true | false = impossible eq
... | false | _ = impossible eq

decode-complete : (b : Bits 8) → decode (encode b) ≡ just b
decode-complete b = refl

encode-injective : (a b : Bits 8) → encode a ≡ encode b → a ≡ b
encode-injective a b eq = cong payload eq

-- Rejection is a universal consequence of the acceptance theorem.
noncanonical-refused : (w : Word) →
  ((b : Bits 8) → w ≡ encode b → Empty) → decode w ≡ nothing
noncanonical-refused w notCanonical with decode w in result
... | nothing = refl
... | just b with notCanonical b (decode-sound w b result)
... | ()
