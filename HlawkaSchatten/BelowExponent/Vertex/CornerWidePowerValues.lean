/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CornerPowerData.WideAxis
public import Mathlib.Data.Rat.Floor

/-! Lookup by exact magnitude for endpoints and midpoints of closed Grid B spans. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def outerWideAxisIndex (x : ℚ) : Nat := ⌊512*|x|⌋.toNat

def outerWideAxisNode (i : Nat) : ℚ := (i : ℚ)/512

def outerWideAxisReady (x : ℚ) : Bool :=
  decide (outerWideAxisIndex x ≤ 512 ∧ outerWideAxisNode (outerWideAxisIndex x) = |x|)

def outerWideAxisSample (i : Nat) : RatBounds :=
  let block := (outerWideQTable[i / 64]?).getD #[]
  (block[i % 64]?).getD (RatBounds.point 0)

def outerWideAxisQAt (x : ℚ) : RatBounds := outerWideAxisSample (outerWideAxisIndex x)

end HlawkaSchatten.BelowExponent.Vertex
