-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- Bv.agda — machine words and the bitvector/integer bridge (spec §4.3.1).
--
-- Written against Agda's builtins only, with all arithmetic defined here, so
-- the development stays inside the Dedukti-CIC subset: indexed inductives and
-- structural recursion, no cubical primitives, no rewrite rules, no
-- inductive-recursive definitions, no axioms, no holes.
--
--   agda --safe --without-K Bv.agda
--
-- The point: SMT solvers reason about *mathematical* integers, Zig computes on
-- *machine words*. Every confusion between the two is a soundness hole. The
-- bridge is made explicit:
--
--   Word            = Fin 2^64          (a number *together with* its bound)
--   toNat           = the underlying number
--   fromNat x p     = the word, requiring the range proof p
--   toNat-<         = every word is in range            (no wraparound exists)
--   fromNat-toNat   = the coercion is a section         (no silent wrap)
--   no-bound        = 2^64 is *not* a word              (the obligation is real)
--
-- `fromNat-toNat` is the licence to read a `bv2nat` coercion as an integer:
-- on the image of `fromNat` the coercion loses nothing. Outside that image
-- there is no proof to supply, which is exactly the `@intCast` range obligation
-- that the SMT side must discharge.

module Bv where

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl
open import Agda.Builtin.Bool using (Bool; true; false)

--------------------------------------------------------------------------------
-- Order, defined here rather than imported
--------------------------------------------------------------------------------

infix 4 _≤_ _<_

data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n _ = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

<-trans : ∀ {a b c} → a < b → b ≤ c → a < c
<-trans p q = ≤-trans p q

--------------------------------------------------------------------------------
-- The empty type and negation: the shape of every refuted obligation
--------------------------------------------------------------------------------

data ⊥ : Set where

¬_ : Set → Set
¬ P = P → ⊥

--------------------------------------------------------------------------------
-- Fin: the word type
--------------------------------------------------------------------------------

data Fin : Nat → Set where
  fzero : ∀ {n} → Fin (suc n)
  fsuc  : ∀ {n} → Fin n → Fin (suc n)

toNat : ∀ {n} → Fin n → Nat
toNat fzero    = zero
toNat (fsuc i) = suc (toNat i)

-- `fromNat n x p` builds a Fin n from x and a proof that x fits.
fromNat : ∀ {n} → (x : Nat) → x < n → Fin n
fromNat {suc n} zero    (s≤s z≤n) = fzero
fromNat {suc n} (suc x) (s≤s p) = fsuc (fromNat x p)

--------------------------------------------------------------------------------
-- Round-trip lemmas: the bridge is a section, not a retraction
--------------------------------------------------------------------------------

toNat-< : ∀ {n} (w : Fin n) → toNat w < n
toNat-< fzero    = s≤s z≤n
toNat-< (fsuc w) = s≤s (toNat-< w)

fromNat-toNat : ∀ {n} (w : Fin n) → (p : toNat w < n) → fromNat (toNat w) p ≡ w
fromNat-toNat fzero    (s≤s z≤n) = refl
fromNat-toNat (fsuc w) (s≤s p) = cong fsuc (fromNat-toNat w p)

toNat-fromNat : ∀ {n} (x : Nat) (p : x < n) → toNat (fromNat x p) ≡ x
toNat-fromNat zero    (s≤s z≤n) = refl
toNat-fromNat (suc x) (s≤s p) = cong suc (toNat-fromNat x p)

--------------------------------------------------------------------------------
-- Word = 64-bit machine integer
--------------------------------------------------------------------------------

2^_ : Nat → Nat
2^ zero    = suc zero
2^ suc k   = 2 * (2^ k)

2^64 : Nat
2^64 = 2^ 64

Word : Set
Word = Fin 2^64

Bound : Nat → Set
Bound x = x < 2^64

word : (x : Nat) → Bound x → Word
word x p = fromNat x p

unword : Word → Nat
unword = toNat

-- Every word is an in-range number: there is no "wrapped" word to worry about.
word-bound : (w : Word) → Bound (unword w)
word-bound = toNat-<

-- The coercion `Nat → Word` is injective on its domain of definition. This is
-- the theorem that licenses reading the bitvector as an integer *after* the
-- range obligation has been discharged, and only then.
word-inj : (x : Nat) (p : Bound x) → unword (word x p) ≡ x
word-inj = toNat-fromNat

--------------------------------------------------------------------------------
-- The obligation is real: 2^64 is not a word
--------------------------------------------------------------------------------

<irrefl : ∀ (n : Nat) → ¬ (n < n)
<irrefl zero    ()
<irrefl (suc n) (s≤s p) = <irrefl n p

no-bound-2^64 : ¬ (Bound 2^64)
no-bound-2^64 = <irrefl 2^64
