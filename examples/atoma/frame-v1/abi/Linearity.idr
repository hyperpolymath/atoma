||| SPDX-License-Identifier: MPL-2.0
||| SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
|||
||| Linearity.idr — the negative half of the QTT discipline.
|||
||| Each `failing` block asserts that a specific misuse does *not* typecheck.
||| They are excluded from FrameAbi.ipkg on purpose: a `failing` block whose
||| expected message does not match the compiler's real diagnostic is itself a
||| compile error, so the messages must be reconciled on the machine that has
||| Idris2 before these can be a gate. Run by hand with
|||
|||   idris2 --check abi/Linearity.idr
|||
||| and then tighten the expected messages to the real ones, at which point this
||| file joins gate F0.1.

module Linearity

import FrameAbi

%default total

||| A correct consumer: the handle is used exactly once. This one must pass.
public export
consumeOnce : Handle -> PtrOutFrame -> IO (Either Bits32 ())
consumeOnce h out = parseFrame h 0 out

||| Dropping a linear handle: must be rejected.
failing "unused linear"
  public export
  consumeZero : Handle -> PtrOutFrame -> IO (Either Bits32 ())
  consumeZero h out = pure (Right ())

||| Using a linear handle twice: must be rejected.
failing "linear"
  public export
  consumeTwice : Handle -> PtrOutFrame -> IO (Either Bits32 ())
  consumeTwice h out = do
    _ <- parseFrame h 0 out
    parseFrame h 0 out
