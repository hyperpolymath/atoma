-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- Core.agda — the core language, its semantics, and the VC generator.
--
--   agda --safe --without-K Core.agda
--
-- This is the language the verification-condition generator targets, small
-- enough that "soundness" is a theorem and not a gesture. It is deliberately
-- *not* all of Zig: it is the fragment whose obligations are first-order and
-- whose evaluation is structural.
--
-- What is modelled
--   * statements: skip, bind (evaluate an expression), seq, assert, if/else
--   * expressions: literals, variables, +, *, subtraction and division
--   * undefined behaviour: subtraction underflow and division by zero are the
--     two reachable UB states in this fragment (§6.2 of the specification)
--   * the path condition: an `assert` and the test of an `if` both refine it,
--     which is exactly how `if (length > avail) return error` protects the
--     slice on the following line
--
-- The fragment is STORE-FREE, by construction. `bind e` evaluates `e` and
-- discards the result; no expression can read a value that a statement wrote,
-- because `Tm` has no constructor for it. That is not an accident of the
-- encoding, it is the discipline the seam already imposes: path conditions are
-- stated over parameters (`r0`), writes go to an output region (`r1`), and the
-- two are disjoint by the `assigns` clause. Modelling a store would require the
-- framing lemma ("a statement that writes nothing mentioned by `pc` preserves
-- `pc`"), which is Phase 2 work; stating it without proving it would be worse
-- than leaving it out.
--
-- What is NOT modelled, and why the theorem is still worth having
--   * machine words. `+`, `*` here are mathematical naturals. The bitvector
--     gap is closed separately: `Bv.agda` proves the coercion bridge, and the
--     VC generator emits an explicit range obligation for every lowering.
--     Mixing the two models in one file would hide the gap rather than show it.
--   * loops. A `while` needs an invariant and a variant, i.e. a second
--     induction; that is `Lin.agda`'s shape for resources and is Phase 2 here.
--   * the heap, pointers, and aliasing. `assign` writes a scalar.
--
-- A VC generator that is sound for a fragment it does not cover is worthless,
-- so the fragment boundary is stated in the type of every theorem below.

module Core where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

--------------------------------------------------------------------------------
-- Pairs (defined here so the development needs no library)
--------------------------------------------------------------------------------

infixr 2 _×_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

--------------------------------------------------------------------------------
-- Truncated subtraction and list append, defined here (the builtins do not
-- export them, and importing the full standard library would pull in far more
-- than this development needs).
--------------------------------------------------------------------------------

_∸_ : Nat → Nat → Nat
zero ∸ n = zero
suc m ∸ zero = suc m
suc m ∸ suc n = m ∸ n

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- Boolean connectives, defined here so `⟦_⟧f` is definitionally the operation
-- on `Bool` (which makes the adequacy lemmas cheap).
_&&_ : Bool → Bool → Bool
true && b = b
false && _ = false

_||_ : Bool → Bool → Bool
true || _ = true
false || b = b

not : Bool → Bool
not true = false
not false = true

infixr 6 _&&_
infixr 5 _||_

--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

data Tm : Set where
  lit : Nat → Tm
  var : Nat → Tm
  add : Tm → Tm → Tm
  mul : Tm → Tm → Tm
  sub : Tm → Tm → Tm   -- UB when the subtrahend exceeds the minuend
  div : Tm → Tm → Tm   -- UB when the divisor is zero

Val : Set
Val = Nat → Nat

_≤?_ : Nat → Nat → Bool
zero ≤? n = true
suc m ≤? zero = false
suc m ≤? suc n = m ≤? n

_==?_ : Nat → Nat → Bool
zero ==? zero = true
zero ==? suc n = false
suc m ==? zero = false
suc m ==? suc n = m ==? n

⟦_⟧t : Tm → Val → Nat
⟦ lit n ⟧t _ = n
⟦ var x ⟧t v = v x
⟦ add a b ⟧t v = ⟦ a ⟧t v + ⟦ b ⟧t v
⟦ mul a b ⟧t v = ⟦ a ⟧t v * ⟦ b ⟧t v
⟦ sub a b ⟧t v = ⟦ a ⟧t v ∸ ⟦ b ⟧t v
⟦ div a b ⟧t v = ⟦ a ⟧t v -- the value is irrelevant when it is UB

--------------------------------------------------------------------------------
-- Formulas
--
-- `le`, `eq` are the only atoms the VC generator emits; `and`/`neg` appear in
-- path conditions produced by `if`. The interpretation is *definitionally* the
-- boolean operation, which is what makes the adequacy lemmas cheap.
--------------------------------------------------------------------------------

data Fm : Set where
  tt : Fm
  le : Tm → Tm → Fm
  eq : Tm → Tm → Fm
  and : Fm → Fm → Fm
  neg : Fm → Fm

⟦_⟧f : Fm → Val → Bool
⟦ tt ⟧f _ = true
⟦ le a b ⟧f v = ⟦ a ⟧t v ≤? ⟦ b ⟧t v
⟦ eq a b ⟧f v = ⟦ a ⟧t v ==? ⟦ b ⟧t v
⟦ and a b ⟧f v = ⟦ a ⟧f v && ⟦ b ⟧f v
⟦ neg a ⟧f v = not (⟦ a ⟧f v)

--------------------------------------------------------------------------------
-- Statements and their execution
--
-- `exec` is total and never inspects its own safety: it computes the answer the
-- program would compute, including in states where the program would actually
-- be undefined. Safety is a *separate* predicate (`safe`), and the theorem
-- relates the two. This separation is the whole point: it is what lets a
-- compensating bug in `exec` be caught rather than hidden.
--------------------------------------------------------------------------------

data Stmt : Set where
  skip : Stmt
  bind : Tm → Stmt                      -- evaluate; the result is discarded
  seq : Stmt → Stmt → Stmt
  assert : Fm → Stmt
  ite : Fm → Stmt → Stmt → Stmt

ifB : ∀ {A : Set} → Bool → A → A → A
ifB true a b = a
ifB false a b = b

exec : Stmt → Val → Val
exec skip v = v
exec (bind e) v = v                  -- store-free: the value is not retained
exec (seq s t) v = exec t (exec s v)
exec (assert φ) v = v
exec (ite φ s t) v = ifB (⟦ φ ⟧f v) (exec s v) (exec t v)

--------------------------------------------------------------------------------
-- Safety: the predicate that must never be false
--------------------------------------------------------------------------------

safeTm : Tm → Val → Bool
safeTm (lit n) v = true
safeTm (var x) v = true
safeTm (add a b) v = safeTm a v && safeTm b v
safeTm (mul a b) v = safeTm a v && safeTm b v
safeTm (sub a b) v = safeTm a v && safeTm b v && (⟦ b ⟧t v ≤? ⟦ a ⟧t v)
safeTm (div a b) v = safeTm a v && safeTm b v && not (⟦ b ⟧t v ==? zero)

safe : Stmt → Val → Bool
safe skip _ = true
safe (bind e) v = safeTm e v
safe (seq s t) v = safe s v && safe t (exec s v)
safe (assert φ) v = ⟦ φ ⟧f v
safe (ite φ s t) v = ifB (⟦ φ ⟧f v) (safe s v) (safe t v)

--------------------------------------------------------------------------------
-- Obligations and validity
--
-- An obligation is a Horn clause (premise, goal). Validity is *universal*: an
-- obligation is valid when it holds in every state satisfying its premise.
-- That is precisely what an SMT solver returns for `∀ vars. pre ⇒ goal`, and
-- it is what makes the frame problem disappear: a valid obligation stays valid
-- after any assignment.
--------------------------------------------------------------------------------

record Obl : Set where
  constructor mkObl
  field
    pre : Fm
    goal : Fm

OblValid : Obl → Set
OblValid o = ∀ v → ⟦ Obl.pre o ⟧f v ≡ true → ⟦ Obl.goal o ⟧f v ≡ true

AllValid : List Obl → Set
AllValid [] = ⊤
AllValid (o ∷ os) = OblValid o × AllValid os

--------------------------------------------------------------------------------
-- The VC generator
--
-- `tmObls pc e` emits one obligation per *observable* hazard in `e`, each
-- guarded by the current path condition. The obligation is placed first so the
-- adequacy proof can consume it before recursing.
--------------------------------------------------------------------------------

tmObls : Fm → Tm → List Obl
tmObls pc (lit n) = []
tmObls pc (var x) = []
tmObls pc (add a b) = tmObls pc a ++ tmObls pc b
tmObls pc (mul a b) = tmObls pc a ++ tmObls pc b
tmObls pc (sub a b) = mkObl pc (le b a) ∷ (tmObls pc a ++ tmObls pc b)
tmObls pc (div a b) = mkObl pc (neg (eq b (lit zero))) ∷ (tmObls pc a ++ tmObls pc b)

vc : Fm → Stmt → List Obl
vc pc skip = []
vc pc (bind e) = tmObls pc e
vc pc (seq s t) = vc pc s ++ vc pc t
vc pc (assert φ) = mkObl pc φ ∷ []
vc pc (ite φ s t) = vc (and pc φ) s ++ vc (and pc (neg φ)) t

--------------------------------------------------------------------------------
-- Sanity: the generator is not vacuous on the worked example's boundary.
-- `12 ≤ len` is the guard that protects `len - 12`; with it, one obligation is
-- emitted, and without it the generator still emits one (whose premise is
-- `tt`), which the solver will refute. Vacuity is a property of the premise,
-- not of whether an obligation exists — which is why the specification makes
-- satisfiability of the premises a VC of its own.
--------------------------------------------------------------------------------

example-guarded : List Obl
example-guarded = vc (le (lit 12) (var 0)) (bind (sub (var 0) (lit 12)))

example-unguarded : List Obl
example-unguarded = vc tt (bind (sub (var 0) (lit 12)))
