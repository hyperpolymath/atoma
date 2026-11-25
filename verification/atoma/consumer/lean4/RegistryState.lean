-- SPDX-License-Identifier: MPL-2.0
namespace RegistryState
inductive Slot where | rest | mcp
structure State (A : Type) where
  rest : Option A
  mcp : Option A
  active : Bool
def lookup {A} (k : Slot) (s : State A) := match k with
  | .rest => s.rest | .mcp => s.mcp
def other : Slot → Slot | .rest => .mcp | .mcp => .rest
def put {A} (k : Slot) (e : Option A) (s : State A) : State A := match k with
  | .rest => ⟨e, s.mcp, s.active⟩ | .mcp => ⟨s.rest, e, s.active⟩
def mark {A} (s : State A) (b : Bool) : State A := ⟨s.rest, s.mcp, b⟩
inductive Result (A : Type) where
  | refused : State A → Result A
  | called : A → State A → Result A
def begin {A} (k : Slot) (s : State A) : Result A :=
  match s.active with
  | true => .refused s
  | false => match lookup k s with
    | none => .refused s | some e => .called e (mark s true)
theorem updateFrame {A} (k : Slot) (e : Option A) (s : State A) :
    lookup (other k) (put k e s) = lookup (other k) s := by cases k <;> rfl
theorem updateIdentity {A} (k : Slot) (e : Option A) (s : State A) :
    lookup k (put k e s) = e := by cases k <;> rfl
theorem beginIdentity {A} (k : Slot) (r m : Option A) (e : A)
    (h : lookup k (State.mk r m false) = some e) :
    begin k (State.mk r m false) = .called e (State.mk r m true) := by
  change (match lookup k (State.mk r m false) with
    | none => Result.refused (State.mk r m false)
    | some x => Result.called x (State.mk r m true)) = _
  rw [h]
theorem reentrantRefused {A} (k : Slot) (s : State A) :
    begin k (mark s true) = .refused (mark s true) := rfl
theorem normalReturnFrame {A} (k : Slot) (s : State A) :
    lookup k (mark s false) = lookup k s := by cases k <;> rfl
theorem normalReturnIdle {A} (s : State A) : (mark s false).active = false := rfl
#print axioms updateFrame
#print axioms updateIdentity
#print axioms beginIdentity
#print axioms reentrantRefused
#print axioms normalReturnFrame
#print axioms normalReturnIdle
end RegistryState

