-- SPDX-License-Identifier: MPL-2.0
import Init.Data.List.Nat.TakeDrop
namespace HeapOwnership
-- Ghost protocol only; it does not validate or confer authority over raw pointers.
inductive Allocation where
  | vacant
  | live (bytes : List Nat) (retained readers : Nat)
inductive Operation where
  | acquire (bytes : List Nat)
  | retain | dropRetention | borrowRead | returnRead | release
  | writeBytes (bytes : List Nat)
open Allocation Operation
def cellStep : Operation → Allocation → Option Allocation
  | acquire bytes, vacant => some (live bytes 0 0)
  | retain, live bytes retained readers => some (live bytes (retained+1) readers)
  | dropRetention, live bytes (retained+1) readers => some (live bytes retained readers)
  | borrowRead, live bytes retained readers => some (live bytes retained (readers+1))
  | returnRead, live bytes retained (readers+1) => some (live bytes retained readers)
  | release, live _ 0 0 => some vacant
  | writeBytes bytes, live _ retained 0 => some (live bytes retained 0)
  | _, _ => none
abbrev Heap := Nat → Allocation
def replace (h : Heap) (addr : Nat) (value : Allocation) : Heap :=
  fun key => if key = addr then value else h key
def run (op : Operation) (h : Heap) (addr : Nat) : Bool × Heap :=
  match cellStep op (h addr) with
  | none => (false,h)
  | some value => (true,replace h addr value)
def readBytes : Allocation → Option (List Nat)
  | vacant => none
  | live bytes _ _ => some bytes
def thenCell (first second : Operation) (cell : Allocation) : Option Allocation :=
  match cellStep first cell with
  | none => none
  | some next => cellStep second next
def bytesAfter (op : Operation) (cell : Allocation) : Option (List Nat) :=
  match cellStep op cell with
  | none => none
  | some next => readBytes next

theorem releaseBorrowedRefused (bytes : List Nat) (retained readers : Nat) :
    cellStep release (live bytes retained (readers+1)) = none := by
  cases retained <;> rfl
theorem releaseRetainedRefused (bytes : List Nat) (retained readers : Nat) :
    cellStep release (live bytes (retained+1) readers) = none := rfl
theorem writeBorrowedRefused (bytes old : List Nat) (retained readers : Nat) :
    cellStep (writeBytes bytes) (live old retained (readers+1)) = none := rfl
theorem failedPreserves (op : Operation) (h : Heap) (addr key : Nat)
    (refused : cellStep op (h addr) = none) : (run op h addr).2 key = h key := by
  simp only [run, refused]
theorem borrowReturnCell (bytes : List Nat) (retained readers : Nat) :
    thenCell borrowRead returnRead (live bytes retained readers) = some (live bytes retained readers) := rfl
theorem borrowPreservesBytes (bytes : List Nat) (retained readers : Nat) :
    bytesAfter borrowRead (live bytes retained readers) = readBytes (live bytes retained readers) := rfl
theorem releaseRemovesOwned (h : Heap) (addr : Nat) (bytes : List Nat)
    (owned : h addr = live bytes 0 0) : (run release h addr).2 addr = vacant := by
  simp only [run, owned, cellStep, replace, if_pos rfl]
theorem releaseFramesOther (h : Heap) (addr key : Nat) (bytes : List Nat)
    (owned : h addr = live bytes 0 0) (other : key ≠ addr) : (run release h addr).2 key = h key := by
  simp only [run, owned, cellStep, replace, if_neg other]
theorem acquireLiveRefused (bytes old : List Nat) (retained readers : Nat) :
    cellStep (acquire bytes) (live old retained readers) = none := rfl

def borrowedSpan (offset count : Nat) (bytes : List Nat) : List Nat :=
  (bytes.drop offset).take count
theorem spanLength (offset count : Nat) (bytes : List Nat)
    (fits : offset+count ≤ bytes.length) : (borrowedSpan offset count bytes).length = count := by
  rw [borrowedSpan, List.length_take, List.length_drop]
  apply Nat.min_eq_left
  apply Nat.le_sub_of_add_le
  simpa only [Nat.add_comm] using fits

#print axioms releaseBorrowedRefused
#print axioms releaseRetainedRefused
#print axioms writeBorrowedRefused
#print axioms failedPreserves
#print axioms borrowReturnCell
#print axioms borrowPreservesBytes
#print axioms releaseRemovesOwned
#print axioms releaseFramesOther
#print axioms acquireLiveRefused
#print axioms spanLength
end HeapOwnership
