-- SPDX-License-Identifier: MPL-2.0
{-# OPTIONS --safe --without-K --cubical-compatible #-}
module HeapOwnership where
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Equality

-- This is a ghost region/permission protocol, not a native pointer validator.
-- A caller must possess authority for its region; raw aliases and the mapping
-- from machine addresses to these region identities remain external premises.
data Allocation : Set where
  vacant : Allocation
  live : (bytes : List Nat) (retained readers : Nat) → Allocation

data Operation : Set where
  acquire write-bytes : List Nat → Operation
  retain drop-retention borrow-read return-read release : Operation

cell-step : Operation → Allocation → Maybe Allocation
cell-step (acquire bytes) vacant = just (live bytes zero zero)
cell-step (acquire bytes) (live old retained readers) = nothing
cell-step retain (live bytes retained readers) = just (live bytes (suc retained) readers)
cell-step drop-retention (live bytes (suc retained) readers) = just (live bytes retained readers)
cell-step borrow-read (live bytes retained readers) = just (live bytes retained (suc readers))
cell-step return-read (live bytes retained (suc readers)) = just (live bytes retained readers)
cell-step release (live bytes retained (suc readers)) = nothing
cell-step release (live bytes (suc retained) zero) = nothing
cell-step release (live bytes zero zero) = just vacant
cell-step (write-bytes bytes) (live old retained zero) = just (live bytes retained zero)
cell-step (write-bytes bytes) (live old retained (suc readers)) = nothing
cell-step _ _ = nothing

Heap : Set
Heap = Nat → Allocation

replace : Heap → Nat → Allocation → Heap
replace h zero value zero = value
replace h zero value (suc key) = h (suc key)
replace h (suc addr) value zero = h zero
replace h (suc addr) value (suc key) = replace (λ n → h (suc n)) addr value key

record Result : Set where
  constructor result
  field
    succeeded : Bool
    store : Heap
open Result public

run : Operation → Heap → Nat → Result
run op h addr with cell-step op (h addr)
... | nothing = result false h
... | just value = result true (replace h addr value)

read-bytes : Allocation → Maybe (List Nat)
read-bytes vacant = nothing
read-bytes (live bytes _ _) = just bytes

then-cell : Operation → Operation → Allocation → Maybe Allocation
then-cell first second cell with cell-step first cell
... | nothing = nothing
... | just next = cell-step second next
bytes-after : Operation → Allocation → Maybe (List Nat)
bytes-after op cell with cell-step op cell
... | nothing = nothing
... | just next = read-bytes next

data Empty : Set where
absurd : {A : Set} → Empty → A
absurd ()
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

replace-hit : (h : Heap) (addr : Nat) (value : Allocation) → replace h addr value addr ≡ value
replace-hit h zero value = refl
replace-hit h (suc addr) value = replace-hit (λ n → h (suc n)) addr value

replace-frame : (h : Heap) (addr key : Nat) (value : Allocation) →
  (key ≡ addr → Empty) → replace h addr value key ≡ h key
replace-frame h zero zero value neq = absurd (neq refl)
replace-frame h zero (suc key) value neq = refl
replace-frame h (suc addr) zero value neq = refl
replace-frame h (suc addr) (suc key) value neq =
  replace-frame (λ n → h (suc n)) addr key value (λ eq → neq (cong suc eq))

release-borrowed-refused : ∀ bytes retained readers →
  cell-step release (live bytes retained (suc readers)) ≡ nothing
release-borrowed-refused bytes retained readers = refl

release-retained-refused : ∀ bytes retained readers →
  cell-step release (live bytes (suc retained) readers) ≡ nothing
release-retained-refused bytes retained zero = refl
release-retained-refused bytes retained (suc readers) = refl

write-borrowed-refused : ∀ bytes old retained readers →
  cell-step (write-bytes bytes) (live old retained (suc readers)) ≡ nothing
write-borrowed-refused bytes old retained readers = refl

failed-preserves : ∀ op h addr key → cell-step op (h addr) ≡ nothing →
  store (run op h addr) key ≡ h key
failed-preserves op h addr key refused rewrite refused = refl

borrow-return-cell : ∀ bytes retained readers →
  then-cell borrow-read return-read (live bytes retained readers) ≡ just (live bytes retained readers)
borrow-return-cell bytes retained readers = refl

borrow-preserves-bytes : ∀ bytes retained readers →
  bytes-after borrow-read (live bytes retained readers) ≡ read-bytes (live bytes retained readers)
borrow-preserves-bytes bytes retained readers = refl

release-removes-owned : ∀ h addr bytes → h addr ≡ live bytes zero zero →
  store (run release h addr) addr ≡ vacant
release-removes-owned h addr bytes owned rewrite owned = replace-hit h addr vacant

release-frames-other : ∀ h addr key bytes → h addr ≡ live bytes zero zero →
  (key ≡ addr → Empty) → store (run release h addr) key ≡ h key
release-frames-other h addr key bytes owned neq rewrite owned = replace-frame h addr key vacant neq

acquire-live-refused : ∀ bytes old retained readers →
  cell-step (acquire bytes) (live old retained readers) ≡ nothing
acquire-live-refused bytes old retained readers = refl

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)
take : {A : Set} → Nat → List A → List A
take zero xs = []
take (suc n) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs
drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc n) [] = []
drop (suc n) (_ ∷ xs) = drop n xs
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

-- Machine-usize/address representability is an additional native premise.
borrowed-span : Nat → Nat → List Nat → List Nat
borrowed-span offset count bytes = take count (drop offset bytes)

span-length : ∀ offset count bytes → offset + count ≤ length bytes →
  length (borrowed-span offset count bytes) ≡ count
span-length zero zero bytes fits = refl
span-length zero (suc count) [] ()
span-length zero (suc count) (b ∷ bytes) (s≤s fits) = cong suc (span-length zero count bytes fits)
span-length (suc offset) count [] ()
span-length (suc offset) count (b ∷ bytes) (s≤s fits) = span-length offset count bytes fits
