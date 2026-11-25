-- SPDX-License-Identifier: MPL-2.0
namespace WrapperEffects
structure Registry (α : Type) where
  rest : α
  mcp : α
  active : Bool
def finish (s : Registry α) : Registry α := ⟨s.rest, s.mcp, false⟩
theorem normalReturnFrame (r m : α) (after : Registry α)
    (frame : after = ⟨r, m, true⟩) : finish after = ⟨r, m, false⟩ := by
  cases frame
  rfl
theorem invalidSpanCleanup (r m : α) : finish (Registry.mk r m true) = ⟨r, m, false⟩ := rfl
theorem aliasCounterexample : finish (Registry.mk false true true) = ⟨false, true, false⟩ := rfl
def fold (step : Bool → β → Bool) (s : Bool) : List β → Bool
  | [] => s
  | b :: bs => fold step (step s b) bs
def scan (step : Bool → β → Option Bool) (s : Bool) : List β → Option Bool
  | [] => some s
  | b :: bs => match step s b with
    | none => none
    | some next => scan step next bs
theorem scanRefinesFold (step : Bool → β → Bool) (foreign : Bool → β → Option Bool)
    (contract : ∀ s b, foreign s b = some (step s b)) (bs : List β) :
    ∀ s, scan foreign s bs = some (fold step s bs) := by
  induction bs with
  | nil => intro s; rfl
  | cons b bs ih =>
    intro s
    simp only [scan, contract, fold]
    exact ih (step s b)
#print axioms normalReturnFrame
#print axioms invalidSpanCleanup
#print axioms aliasCounterexample
#print axioms scanRefinesFold
end WrapperEffects
