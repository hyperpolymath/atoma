||| SPDX-License-Identifier: MPL-2.0
||| SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
|||
||| FrameAbi — the normative ABI contract for the frame-v1 worked example.
|||
||| This module is Face A of the contract. It is *the* specification: the Zig
||| implementation, the C header and the SMT obligations are all derived from
||| the values declared here. `frameParse : Contract` is a value; the extractor
||| is `putStr (encode frameParse)`, and the bytes it prints are what
||| `spec/face-a.cspec` contains after canonicalisation.
|||
||| Discipline (checked by CI gate F0.1; see docs/spec/ATOMA-SPEC.adoc):
|||   %default total      — every definition must be total
|||   no escape hatches  — no trust-me casts, no axioms, no skipped
|||                        termination checks (the exact banned identifiers
|||                        are listed in docs/spec/ATOMA-SPEC.adoc §2 and are
|||                        scanned for by the proof-circumvention gate)
|||
||| STATUS: this module has NOT been typechecked in the authoring environment
||| (the Idris2 toolchain is absent there). It is normative text, and
||| `idris2 --typecheck abi/FrameAbi.ipkg` is the Phase 0 entry gate (F0.1).
||| Nothing in this repository claims it compiles until that gate runs.
|||
||| Naming: the toolchain is Atoma; the language it verifies is Zig. The C
||| symbol prefix, the contract namespace and the digest domains all use
||| `atoma` so that one name is load-bearing everywhere.

module FrameAbi

import Data.So

%default total

--------------------------------------------------------------------------------
-- Quantities (QTT: 0 = erased ghost, 1 = linear, W = unrestricted)
--------------------------------------------------------------------------------

public export
data Qty = Q0 | Q1 | QW

public export
renderQty : Qty -> String
renderQty Q0 = "0"
renderQty Q1 = "1"
renderQty QW = "W"

--------------------------------------------------------------------------------
-- Sorts. Deliberately tiny: every sort here is ABI-stable and has a fixed
-- width on every supported target, or is a ghost-only sort that never reaches
-- the wire. `USize` is absent on purpose (see §2.3 of the specification).
--------------------------------------------------------------------------------

public export
data Sort
  = U8 | U16 | U32 | U64
  | Handle          -- an opaque capability token, QTT-quantified
  | SliceU8         -- (ptr, len) pair, ghost length, borrowed region
  | PtrOutFrame     -- a linear write lease into caller-owned memory
  | Unit

public export
renderSort : Sort -> String
renderSort U8 = "u8"
renderSort U16 = "u16"
renderSort U32 = "u32"
renderSort U64 = "u64"
renderSort Handle = "handle"
renderSort SliceU8 = "slice ro u8 r0"
renderSort PtrOutFrame = "ptr out_frame r1"
renderSort Unit = "unit"

--------------------------------------------------------------------------------
-- Terms and formulas.
--
-- `Bound k` is a de Bruijn *level*: k = 0 is the outermost `Forall` binder of
-- the enclosing formula. Levels (not indices) are used because the canonical
-- form prints `%k` and v1 forbids shadowing, so levels and indices coincide and
-- alpha-invariance is obtained by construction rather than by a renaming pass.
--
-- Integers are `Nat`; they are lowered to bitvectors of the declared width by
-- the VC generator, and every lowering emits an explicit range obligation.
--------------------------------------------------------------------------------

public export
data Tm
  = Var String        -- a free name: a parameter or a field of an output
  | Num Nat
  | Len String        -- len(p): the ghost length of a slice parameter
  | TagOf String      -- tag(p): the capability tag of a handle
  | MagicOf String    -- magic(p): the magic field of an output struct
  | PayloadLen String
  | Zeroed String     -- zeroed(p): every byte of *p is 0x00
  | PadOf String      -- pad(p): every padding byte of *p is 0x00
  | Add Tm Tm | Sub Tm Tm | Mul Tm Tm

public export
data Fm
  = Le Tm Tm | Lt Tm Tm | Eq Tm Tm | Neq Tm Tm
  | And Fm Fm | Or Fm Fm | Imp Fm Fm | Not Fm
  | Forall Sort Fm

--------------------------------------------------------------------------------
-- Rendering. Total, structural, and emitting the canonical form directly:
--   * one space between tokens, no trailing spaces
--   * binder rendered as `%k` (R4 of the canonicalisation)
--   * integer literals rendered in decimal without leading zeros (R5)
--------------------------------------------------------------------------------

public export
renderTm : Tm -> String
renderTm (Var s) = s
renderTm (Num n) = show n
renderTm (Len s) = "( len " ++ s ++ " )"
renderTm (TagOf s) = "( tag " ++ s ++ " )"
renderTm (MagicOf s) = "( magic " ++ s ++ " )"
renderTm (PayloadLen s) = "( payload_len " ++ s ++ " )"
renderTm (Zeroed s) = "( zeroed " ++ s ++ " )"
renderTm (PadOf s) = "( pad " ++ s ++ " )"
renderTm (Add a b) = "( + " ++ renderTm a ++ " " ++ renderTm b ++ " )"
renderTm (Sub a b) = "( - " ++ renderTm a ++ " " ++ renderTm b ++ " )"
renderTm (Mul a b) = "( * " ++ renderTm a ++ " " ++ renderTm b ++ " )"

public export
renderFm : Fm -> String
renderFm (Le a b) = "( <= " ++ renderTm a ++ " " ++ renderTm b ++ " )"
renderFm (Lt a b) = "( < " ++ renderTm a ++ " " ++ renderTm b ++ " )"
renderFm (Eq a b) = "( = " ++ renderTm a ++ " " ++ renderTm b ++ " )"
renderFm (Neq a b) = "( != " ++ renderTm a ++ " " ++ renderTm b ++ " )"
renderFm (And a b) = "( and " ++ renderFm a ++ " " ++ renderFm b ++ " )"
renderFm (Or a b) = "( or " ++ renderFm a ++ " " ++ renderFm b ++ " )"
renderFm (Imp a b) = "( => " ++ renderFm a ++ " " ++ renderFm b ++ " )"
renderFm (Not a) = "( not " ++ renderFm a ++ " )"
renderFm (Forall s f) = "( forall ( %0 : " ++ renderSort s ++ " ) " ++ renderFm f ++ " )"

--------------------------------------------------------------------------------
-- Contract structure
--------------------------------------------------------------------------------

public export
record Param where
  constructor MkParam
  name : String
  qty  : Qty
  sort : Sort

public export
renderParam : Param -> String
renderParam p = "param " ++ p.name ++ " " ++ renderQty p.qty ++ " " ++ renderSort p.sort

public export
data Access = Shared | Mutable

public export
data Borrow = MkBorrow String Access String   -- param, access, region

public export
renderBorrow : Borrow -> String
renderBorrow (MkBorrow p a r) =
  "borrow " ++ p ++ " " ++ (case a of
                              Shared  => "shr"
                              Mutable => "mut") ++ " " ++ r

public export
record Bounds where
  constructor MkBounds
  steps : Tm        -- MaxPlus worst-case step count
  hwm   : Nat       -- high-water mark, in bytes of stack

public export
record Contract where
  constructor MkContract
  name     : String
  kind     : String          -- "extern" for a C-ABI export
  abiSym   : String          -- the Zig `export fn` name
  params   : List Param
  borrows  : List Borrow
  requires : List Fm
  ensures  : List Fm
  assigns  : List String     -- regions written
  caps     : List String     -- MPR capability footprint
  bounds   : Bounds

-- A fixed-order concatenation of rendered lines. `lines` is total and its
-- result is exactly the canonical byte string (modulo the trailing newline).
public export
lines : List String -> String
lines [] = ""
lines (x :: xs) = x ++ "\n" ++ lines xs

public export
encode : Contract -> String
encode c =
  lines (["cspec 1",
          "contract " ++ c.name,
          "kind " ++ c.kind,
          "abisym " ++ c.abiSym]
         ++ mapRender renderParam c.params
         ++ mapRender renderBorrow c.borrows
         ++ mapRender renderFm c.requires
         ++ mapRender renderFm c.ensures
         ++ mapRender (\s => "assigns " ++ s) c.assigns
         ++ mapRender (\s => "cap " ++ s) c.caps
         ++ ["bound steps " ++ renderTm (steps c.bounds),
             "bound hwm " ++ show (hwm c.bounds)])
  where
    mapRender : (a -> String) -> List a -> List String
    mapRender f [] = []
    mapRender f (x :: xs) = f x :: mapRender f xs

--------------------------------------------------------------------------------
-- The contract itself
--------------------------------------------------------------------------------

public export
handleTag : Nat
handleTag = 0x41544D31   -- ASCII "ATM1"

public export
frameMagic : Nat
frameMagic = 0x5441      -- the u16 whose little-endian bytes are 'A' 'T'

public export
frameParse : Contract
frameParse =
  MkContract
    { name = "atoma.frame.parse"
    , kind = "extern"
    , abiSym = "atoma_frame_parse"
    , params =
        [ MkParam "h"         QW Handle
        , MkParam "input"     QW SliceU8
        , MkParam "input_len" Q0 U32
        , MkParam "out"       Q1 PtrOutFrame
        ]
    , borrows =
        [ MkBorrow "input" Shared "r0"
        , MkBorrow "out" Mutable "r1"
        ]
    , requires =
        [ Le (Num 12) (Len "input")
        , Eq (Len "input") (Var "input_len")
        , Lt (Var "input_len") (Num 0x100000000)
        , Or (Eq (Var "h") (Var "null")) (Eq (TagOf "h") (Num handleTag))
        ]
    , ensures =
        [ Imp (Eq (Var "res") (Num 0)) (Eq (MagicOf "out") (Num frameMagic))
        , Imp (Eq (Var "res") (Num 0)) (Le (PayloadLen "out") (Sub (Len "input") (Num 12)))
        , Imp (Neq (Var "res") (Num 0)) (Zeroed "out")
        , Eq (PadOf "out") (Num 0)
        ]
    , assigns = ["r1"]
    , caps = ["Read r0", "Write r1"]
    , bounds = MkBounds (Add (Num 12) (Mul (Num 8) (Len "input"))) 64
    }

--------------------------------------------------------------------------------
-- Layout. The Idris2 side *declares*; the Zig compiler *witnesses* (see
-- tools/layout_witness.zig); the seam hash binds the two (gate G5).
--
-- Only the target-independent facts are proved here. `FrameOut` contains a
-- pointer, so its size and the position of `payload` differ between 64-bit and
-- wasm32 — those facts are not provable in Idris2 without a target parameter,
-- and pretending otherwise is how ABI bugs happen. They live in the witnessed
-- layout table instead.
--------------------------------------------------------------------------------

public export
record Field where
  constructor MkField
  fname  : String
  offset : Nat
  width  : Nat
  align  : Nat

public export
data Aligned : (off, align : Nat) -> Type where
  MkAligned : (k : Nat) -> (0 prf : off = k * align) -> Aligned off align

public export
endOf : List Field -> Nat
endOf [] = 0
endOf (f :: fs) =
  let e    = offset f + width f
      rest = endOf fs in
  if e > rest then e else rest

public export
frameHeaderFields : List Field
frameHeaderFields =
  [ MkField "magic"    0  2 2
  , MkField "length"   2  2 2
  , MkField "flags"    4  1 1
  , MkField "tag"      5  1 1
  , MkField "crc"      8  4 4
  , MkField "reserved" 12 2 2
  ]

||| Every field starts on its natural alignment.
public export
headerFieldsAligned :
     Aligned 0 2
  -> Aligned 2 2
  -> Aligned 4 1
  -> Aligned 5 1
  -> Aligned 8 4
  -> Aligned 12 2
  -> ()
headerFieldsAligned _ _ _ _ _ _ = ()

public export
headerAligned : Aligned 0 2
headerAligned = MkAligned 0 Refl

public export
lengthAligned : Aligned 2 2
lengthAligned = MkAligned 1 Refl

public export
flagsAligned : Aligned 4 1
flagsAligned = MkAligned 4 Refl

public export
tagAligned : Aligned 5 1
tagAligned = MkAligned 5 Refl

public export
crcAligned : Aligned 8 4
crcAligned = MkAligned 2 Refl

public export
reservedAligned : Aligned 12 2
reservedAligned = MkAligned 6 Refl

||| The struct ends exactly at 16 bytes: no trailing slack, no field past 16.
public export
headerEndsAt : So (endOf frameHeaderFields == 16)
headerEndsAt = Oh

||| The struct size is a multiple of its alignment (required by the C ABI).
public export
headerSizeAligned : Aligned 16 4
headerSizeAligned = MkAligned 4 Refl

--------------------------------------------------------------------------------
-- The seam. These are the only foreign imports in the module, and each is
-- pinned to a symbol that exists in src/frame_parse.zig.
--------------------------------------------------------------------------------

public export
data Handle : Type where
  MkHandle : (ptr : Bits64) -> (0 nonNull : So (ptr /= 0)) -> Handle

||| Parse one frame. Linear in the handle and in the output lease: the QTT
||| quantities mean an implementation that forgets to consume either is a
||| type error, not a runtime leak.
public export
parseFrame :
      (1 h : Handle)
   -> (0 ghostLen : Nat)      -- the length proof, erased
   -> (1 out : PtrOutFrame)
   -> (IO (Either Bits32 ()))
parseFrame h ghostLen out = prim__parse h out

%foreign "C:atoma_frame_parse,libatoma"
prim__parse : Handle -> PtrOutFrame -> IO (Either Bits32 ())

--------------------------------------------------------------------------------
-- What the linearity buys
--------------------------------------------------------------------------------
--
-- The QTT discipline is supposed to reject (a) a handle that is dropped and
-- (b) a handle that is used twice. Both negative tests live in `Linearity.idr`,
-- which is deliberately NOT a module of this package: the expected compiler
-- message has to be reconciled with the real Idris2 diagnostic before the test
-- can be gated, and a `failing` block whose message does not match is itself a
-- compile error. Keeping it out of the package means gate F0.1 stays green
-- while the negative tests remain visible and runnable by hand.
