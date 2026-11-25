{-# OPTIONS --safe --cubical #-}
module WrapperEffectsCubical where
import WrapperEffects as W
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Cubical.Path using (PathP)

toPath : {A : Set} {x y : A} → x ≡ y → PathP (λ _ → A) x y
toPath {x = x} refl _ = x

cleanup-path : {A : Set} (r m : A) →
  PathP (λ _ → W.Registry A) (W.finish (W.registry r m true)) (W.registry r m false)
cleanup-path r m = toPath (W.invalid-span-cleanup r m)

normal-return-path : {A : Set} (r m : A) (out : W.FramedReturn (W.registry r m true)) →
  PathP (λ _ → W.Registry A) (W.finish (W.after out)) (W.registry r m false)
normal-return-path r m out = toPath (W.normal-return-frame r m out)
