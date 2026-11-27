/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-! Exact knots for the balanced-slab extension through \(l=7/125\). -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

def fSlabKnot (i : Fin 157) : ℚ :=
  if i.val < 156 then ((74 + i.val : ℕ) : ℚ) / 4096 else 7 / 125

theorem fSlabKnot_first : fSlabKnot 0 = 74 / 4096 := by norm_num [fSlabKnot]

theorem fSlabKnot_last : fSlabKnot (Fin.last 156) = 7 / 125 := by
  norm_num [fSlabKnot, Fin.last]

set_option maxRecDepth 16000 in
theorem fSlabKnot_bounds : ∀ i : Fin 157, 74 / 4096 ≤ fSlabKnot i ∧ fSlabKnot i ≤ 7 / 125 := by
  decide +kernel

set_option maxRecDepth 16000 in
theorem fSlabKnot_width :
    ∀ i : Fin 156, 0 < fSlabKnot i.succ - fSlabKnot i.castSucc ∧
      fSlabKnot i.succ - fSlabKnot i.castSucc ≤ 1 / 4096 := by
  decide +kernel

end HlawkaSchatten.BelowExponent
