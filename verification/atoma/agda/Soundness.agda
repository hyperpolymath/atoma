-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- Soundness.agda — the adequacy theorem for the VC generator.
--
--   agda --safe --without-K Soundness.agda
--
-- THEOREM (soundness). If every obligation emitted by `vc pc s` is valid, and
-- the initial state satisfies the path condition `pc`, then executing `s` never
-- reaches an undefined state: `safe s v ≡ true`.
--
-- This is the statement §6.4 of the specification makes. It is proved here for
-- the fragment of `Core.agda`: expression evaluation, sequencing, assertion,
-- if/else, and arithmetic that can underflow or divide by zero. It is NOT a
-- theorem about all of Zig, and the specification says so in the same breath.
--
-- In particular the fragment is store-free (see `Core.agda`'s header): the
-- theorem covers every *hazard site*, not data flow between them.
--
-- Why "all obligations valid" and not "obligations hold in this state": a
-- solver returns UNSAT for `premises ∧ ¬goal`, universally quantified over all
-- variables. That is exactly `OblValid`. State-independent validity is also
-- what makes sequencing sound — a valid obligation survives any assignment,
-- so no strongest-postcondition machinery is needed at this level.
--
-- The two halves of the proof:
--   1. `tm-safe`: hazards inside an expression are covered by `tmObls`.
--   2. structural induction over statements, with the path condition refined
--      at `assert` and at each branch of `if`.

module Soundness where

open import Core
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

--------------------------------------------------------------------------------
-- The empty type and basic equality plumbing
--------------------------------------------------------------------------------

data ⊥ : Set where

¬_ : Set → Set
¬ P = P → ⊥

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

true≢false : true ≡ false → ⊥
true≢false ()

false≢true : false ≡ true → ⊥
false≢true ()

not-involves : ∀ b → not (not b) ≡ b
not-involves true = refl
not-involves false = refl

--------------------------------------------------------------------------------
-- Boolean lemmas
--------------------------------------------------------------------------------

&&-elim-l : ∀ a b → (a && b) ≡ true → a ≡ true
&&-elim-l true b p = refl
&&-elim-l false b ()

&&-elim-r : ∀ a b → (a && b) ≡ true → b ≡ true
&&-elim-r true b p = p
&&-elim-r false b ()

&&-intro : ∀ a b → a ≡ true → b ≡ true → (a && b) ≡ true
&&-intro true b refl q = q
&&-intro false b () q

--------------------------------------------------------------------------------
-- The store-free fragment has a trivial state law: a statement never changes
-- the valuation. This is what lets a path condition be used at a later program
-- point — in a store-free fragment, "later" is the same state.
--------------------------------------------------------------------------------

exec-id : ∀ (s : Stmt) (v : Val) → exec s v ≡ v
exec-id skip v = refl
exec-id (bind e) v = refl
exec-id (seq s t) v = trans (exec-id t (exec s v)) (exec-id s v)
exec-id (assert φ) v = refl
exec-id (ite φ s t) v with ⟦ φ ⟧f v
... | true = exec-id s v
... | false = exec-id t v

--------------------------------------------------------------------------------
-- Validity of obligation lists
--------------------------------------------------------------------------------

valid-left : ∀ xs ys → AllValid (xs ++ ys) → AllValid xs
valid-left [] ys p = tt
valid-left (o ∷ os) ys (po , pr) = po , valid-left os ys pr

valid-right : ∀ xs ys → AllValid (xs ++ ys) → AllValid ys
valid-right [] ys p = p
valid-right (o ∷ os) ys (po , pr) = valid-right os ys pr

--------------------------------------------------------------------------------
-- Part 1: expression safety
--
-- Every hazard `tmObls` can see is discharged, so `safeTm` holds.
--------------------------------------------------------------------------------

tm-safe : ∀ (e : Tm) (pc : Fm) (v : Val) →
         ⟦ pc ⟧f v ≡ true →
         AllValid (tmObls pc e) →
         safeTm e v ≡ true

tm-safe (lit n) pc v pp pv = refl

tm-safe (var x) pc v pp pv = refl

tm-safe (add a b) pc v pp pv =
  &&-intro (safeTm a v) (safeTm b v)
    (tm-safe a pc v pp (valid-left (tmObls pc a) (tmObls pc b) pv))
    (tm-safe b pc v pp (valid-right (tmObls pc a) (tmObls pc b) pv))

tm-safe (mul a b) pc v pp pv =
  &&-intro (safeTm a v) (safeTm b v)
    (tm-safe a pc v pp (valid-left (tmObls pc a) (tmObls pc b) pv))
    (tm-safe b pc v pp (valid-right (tmObls pc a) (tmObls pc b) pv))

tm-safe (sub a b) pc v pp (po , pr) =
  -- the obligation is `pc ⇒ b ≤ a`, placed first by `tmObls`
  &&-intro (safeTm a v) (safeTm b v && (⟦ b ⟧t v ≤? ⟦ a ⟧t v))
    (tm-safe a pc v pp (valid-left (tmObls pc a) (tmObls pc b) pr))
    (&&-intro (safeTm b v) (⟦ b ⟧t v ≤? ⟦ a ⟧t v)
      (tm-safe b pc v pp (valid-right (tmObls pc a) (tmObls pc b) pr))
      (po v pp))

tm-safe (div a b) pc v pp (po , pr) =
  -- the obligation is `pc ⇒ ¬(b = 0)`, placed first by `tmObls`
  &&-intro (safeTm a v) (safeTm b v && not (⟦ b ⟧t v ==? zero))
    (tm-safe a pc v pp (valid-left (tmObls pc a) (tmObls pc b) pr))
    (&&-intro (safeTm b v) (not (⟦ b ⟧t v ==? zero))
      (tm-safe b pc v pp (valid-right (tmObls pc a) (tmObls pc b) pr))
      (po v pp))

--------------------------------------------------------------------------------
-- Part 2: the theorem
--------------------------------------------------------------------------------

soundness : ∀ (s : Stmt) (pc : Fm) (v : Val) →
            AllValid (vc pc s) →
            ⟦ pc ⟧f v ≡ true →
            safe s v ≡ true

soundness skip pc v pv pp = refl

soundness (bind e) pc v pv pp = tm-safe e pc v pp pv

soundness (seq s t) pc v pv pp =
  &&-intro (safe s v) (safe t (exec s v))
    (soundness s pc v (valid-left (vc pc s) (vc pc t) pv) pp)
    (soundness t pc (exec s v) (valid-right (vc pc s) (vc pc t) pv)
       (trans (cong (λ w → ⟦ pc ⟧f w) (exec-id s v)) pp))

soundness (assert φ) pc v (po , tt) pp = po v pp

-- `in eq` keeps the scrutinee's equation, which is what the `&&-intro` premise
-- and the `not` case both need; a plain `with` abstracts it away.
soundness (ite φ s t) pc v pv pp with ⟦ φ ⟧f v in eq
... | true =
  soundness s (and pc φ) v
    (valid-left (vc (and pc φ) s) (vc (and pc (neg φ)) t) pv)
    (&&-intro (⟦ pc ⟧f v) (⟦ φ ⟧f v) pp eq)
... | false =
  soundness t (and pc (neg φ)) v
    (valid-right (vc (and pc φ) s) (vc (and pc (neg φ)) t) pv)
    (&&-intro (⟦ pc ⟧f v) (not (⟦ φ ⟧f v)) pp (cong not eq))

--------------------------------------------------------------------------------
-- Corollary: the theorem read as "no undefined behaviour"
--------------------------------------------------------------------------------

no-undefined-behaviour :
  ∀ (s : Stmt) (pc : Fm) (v : Val) →
  AllValid (vc pc s) →
  ⟦ pc ⟧f v ≡ true →
  safe s v ≡ true
no-undefined-behaviour = soundness

--------------------------------------------------------------------------------
-- The worked example, in miniature
--
-- `len - 12`: guarded by `12 ≤ len`, the obligation is valid; unguarded, it is
-- refuted by the same model z3 produced for V1 (`buf_len = 0`).
--------------------------------------------------------------------------------

guarded-valid :
  OblValid (mkObl (le (lit 12) (var 0)) (le (lit 12) (var 0)))
guarded-valid v p = p

-- The guarded program is safe for every state satisfying the guard.
guarded-safe : ∀ (v : Val) → ⟦ le (lit 12) (var 0) ⟧f v ≡ true →
               safe (bind (sub (var 0) (lit 12))) v ≡ true
guarded-safe v p =
  soundness (bind (sub (var 0) (lit 12))) (le (lit 12) (var 0)) v
    (guarded-valid , tt) p

-- Unguarded, the emitted obligation is *not* valid: the state with `len = 0`
-- refutes it. This is the same counterexample the solver returned.
unguarded-not-valid :
  ¬ (OblValid (mkObl tt (le (lit 12) (var 0))))
unguarded-not-valid p = true≢false (sym (p (λ _ → zero) refl))

-- Therefore the unguarded program is not covered by the theorem, which is the
-- correct outcome: `vc` emitted the obligation, and the obligation is false.
unguarded-obligation-is-the-only-one :
  vc tt (bind (sub (var 0) (lit 12)))
    ≡ (mkObl tt (le (lit 12) (var 0)) ∷ [])
unguarded-obligation-is-the-only-one = refl
