/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabMesh

/-! A common weight for each closed F slab. Adjacent groups check both weights at the join. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

def fSlabWeightNum (i : Fin 156) : ℕ :=
  if i.val < 28 then 21 else if i.val < 90 then 23 else
  if i.val < 122 then 25 else 27

def fSlabWeight (i : Fin 156) : ℚ := (fSlabWeightNum i : ℚ)/100

theorem fSlabWeightNum_le (i : Fin 156) : fSlabWeightNum i ≤ 100 := by
  unfold fSlabWeightNum
  split <;> (try split) <;> (try split) <;> decide

set_option maxRecDepth 16000 in
theorem fSlabWeight_bounds : ∀ (i : Fin 156) (cap : Bool),
    21/100 ≤ fSlabWeight i ∧ fSlabWeight i ≤ 27/100 ∧
    37/200 ≤ fSlabWeight i - fSlabKnot (if cap then i.succ else i.castSucc) := by
  decide +kernel

end HlawkaSchatten.BelowExponent
