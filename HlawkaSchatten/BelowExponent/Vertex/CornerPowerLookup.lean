/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import Mathlib.Data.Rat.Floor

/-! Numeric lookup and chord evaluation for the packed outer power table. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def outerKnot (k : Nat) : ℚ := (k : ℚ) / 256

def outerUpperEntry (values : Array (Array ℤ)) (k : Nat) : ℚ :=
  let block := (values[k / 64]?).getD #[]
  (((block[k % 64]?).getD 0 : ℤ) : ℚ) / 2^64

def outerChordIndex (x : ℚ) : Nat := ⌊256 * |x|⌋.toNat

def outerChordFraction (x : ℚ) : ℚ := 256 * |x| - (outerChordIndex x : ℚ)

def outerRpowChord (values : Array (Array ℤ)) (x : ℚ) : ℚ :=
  let j := outerChordIndex x
  let t := outerChordFraction x
  (1-t)*outerUpperEntry values j + t*outerUpperEntry values (j+1)

end HlawkaSchatten.BelowExponent.Vertex
