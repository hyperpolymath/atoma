||| SPDX-License-Identifier: MPL-2.0
||| SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
|||
||| Linearity.idr — the negative half of the QTT discipline.
|||
||| Each `failing` block asserts that a specific misuse does *not* typecheck.
||| Both rejections are part of FrameAbi.ipkg and gate F0.1. These test QTT
||| resource consumption in the model, not the runtime behaviour of Zig.

module Linearity

import FrameAbi

%default total

||| A correct consumer: the handle is used exactly once. This one must pass.
public export
consumeOnce : (1 h : Handle) -> (1 out : OutLease) -> ()
consumeOnce h out = consumeModel h out

-- Dropping a linear handle: must be rejected.
failing "linear"
  public export
  consumeZero : (1 h : Handle) -> (1 out : OutLease) -> ()
  consumeZero h out = ()

-- Using a linear handle twice: must be rejected.
failing "linear"
  public export
  consumeTwice : (1 h : Handle) -> (1 out : OutLease) -> ((), ())
  consumeTwice h out = (consumeModel h out, consumeModel h out)
