-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- Lin.agda — linear-handle cleanup for `defer` / `errdefer` (spec §4.4).
--
--   agda --safe --without-K Lin.agda
--
-- Obligation: a QTT-`1` handle acquired at the top of an `export fn` is
-- consumed exactly once on *every* path — the normal path and every early
-- `return error` path taken by a `try` inside the body.
--
-- Zig gives two handlers with different reachability:
--
--   defer    runs on every exit of the enclosing scope
--   errdefer runs only when the scope is left by an error return
--
-- so the canonical shape
--
--   const h = try open();     -- acquire, quantity 1
--   errdefer close(h);        -- handler, registered after acquisition
--   try step1();              -- may fail
--   try step2();              -- may fail
--   close(h);                 -- explicit consumption on the happy path
--
-- has one textual `close` on the happy path and none on the failure paths, yet
-- must run `close` exactly once on all of them. That is `exactly-once` below,
-- abstract over the number and kind of intermediate steps.
--
-- Failure is sticky: once a step fails, the rest of the scope is skipped (what
-- `try` + early return do) and the `errdefer` handler is the only thing that
-- runs at scope exit. Both halves are part of the model; §6.3 records what the
-- model does and does not cover.

module Lin where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

--------------------------------------------------------------------------------
-- Small helpers
--------------------------------------------------------------------------------

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

true≢false : true ≡ false → ⊥
true≢false ()

ite : ∀ {A : Set} → Bool → A → A → A
ite true  t f = t
ite false t f = f

--------------------------------------------------------------------------------
-- State
--------------------------------------------------------------------------------

record St : Set where
  constructor mkSt
  field rels : Nat          -- how many times the handle has been released
  field failed : Bool       -- whether the scope has already left by an error

open St

initial : St
initial = mkSt zero false

--------------------------------------------------------------------------------
-- The scope: a sequence of steps, each harmless or failing. The happy-path
-- `close` is *structure*, not a step, so no user step can release behind the
-- verifier's back.
--------------------------------------------------------------------------------

data Step : Set where
  work  : Step
  fails : Step

applyStep : St → Step → St
applyStep s work  = s
applyStep s fails = record s { failed = true }

-- Running the scope. `[]` is the point where the happy-path `close` sits:
-- reaching it means the scope did not fail, so the close runs exactly there.
runBody : St → List Step → St
runBody s [] = ite (failed s) s (record s { rels = suc (rels s) })
runBody s (x ∷ xs) = ite (failed s) s (runBody (applyStep s x) xs)

-- The errdefer handler: runs iff the scope failed, and it releases.
handler : St → St
handler s = ite (failed s) (record s { rels = suc (rels s) ; failed = false }) s

whole : List Step → St
whole steps = handler (runBody initial steps)

--------------------------------------------------------------------------------
-- Lemmas
--------------------------------------------------------------------------------

applyStep-rels : ∀ (s : St) (x : Step) → rels (applyStep s x) ≡ rels s
applyStep-rels s work  = refl
applyStep-rels s fails = refl

-- A scope that has already failed runs nothing else.
runBody-dead : ∀ (xs : List Step) (s : St) → failed s ≡ true → runBody s xs ≡ s
runBody-dead [] s q with failed s
... | true  = refl
... | false = ⊥-elim (true≢false (sym q))
runBody-dead (x ∷ xs) s q with failed s
... | true  = refl
... | false = ⊥-elim (true≢false (sym q))

--------------------------------------------------------------------------------
-- Exactly one release on every path.
--
-- Generalised over the starting state so the induction hypothesis applies
-- mid-body; `failed s ≡ false` is the invariant that the scope is still live.
--------------------------------------------------------------------------------

exactly-once :
  ∀ (steps : List Step) (s : St) →
  failed s ≡ false →
  rels (handler (runBody s steps)) ≡ suc (rels s)

exactly-once [] s p
  rewrite p = refl

exactly-once (work ∷ xs) s p
  rewrite p = exactly-once xs s p

exactly-once (fails ∷ xs) s p
  rewrite p =
    cong (λ t → rels (handler t)) (runBody-dead xs (record s { failed = true }) refl)

--------------------------------------------------------------------------------
-- Headline: every execution of the canonical scope releases exactly once,
-- whether it succeeds, fails on the first step, or fails on any later step.
--------------------------------------------------------------------------------

theorem-rel-once : ∀ (steps : List Step) → rels (whole steps) ≡ suc zero
theorem-rel-once steps = exactly-once steps initial refl

-- Two concrete traces, so the theorem is not vacuous: the empty scope (happy
-- path via the explicit close) and a scope that fails after one step (via the
-- handler). Both release exactly once.
trace-happy : rels (whole []) ≡ suc zero
trace-happy = refl

trace-failed : rels (whole (work ∷ fails ∷ [])) ≡ suc zero
trace-failed = refl
