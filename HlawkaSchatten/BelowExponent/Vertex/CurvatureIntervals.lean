/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CoefficientIntervals

/-! Rational direction- and component-wise upper curvature tests. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

theorem qInterval_mem : qInterval.Contains criticalQ := by
  apply DyadicBounds.ofRat_mem
  constructor <;> norm_num <;> linarith only [criticalQ_bracket.1, criticalQ_bracket.2]

theorem curvatureInterval_mem {c : ParameterCell} {roots : Fin 3 → RatBounds} {a b η : ℝ}
    (ht : c.Contains a b η) (hη : 0 ≤ η) (k i : Fin 3)
    (hR : ∀ j, (radicalInterval c roots k j).Contains (radicalJet k ![a,b,η] j)) :
    (curvatureInterval (axisCoefficientIntervals c roots k) i).Contains (curvatureBudget criticalQ
      (fun j => (parameterDJet k ![a,b,η] j).second)
      (fun j l => (parameterHJet k ![a,b,η] j l).second) i) := by
  have hd := (parameterDInterval_mem ht hη k i hR).2.2
  have h (j l : Fin 3) := (parameterHInterval_mem ht hη k j l hR).2.2
  have hf := hd.add (qInterval_mem.mul (h i i))
  have hr := (h i (i+1)).abs.add (h i (i+2)).abs
  have hc := (h (i+1) i).abs.add (h (i+2) i).abs
  simpa only [curvatureInterval, curvatureBudget, add_assoc] using (hf.add hr).add
    ((qInterval_mem.sub DyadicBounds.one_mem).mul hc)

/-- The real consequences of one successful subcell check on the actual chart. -/
theorem subcellCurvatureOK_sound {c parent : ParameterCell} {roots : Fin 3 → RatBounds}
    {maxima : Fin 3 → Fin 3 → ℚ} {weightFloor : ℚ} {a b η : ℝ}
    (ht : c.Contains a b η) (hp : parent.Contains a b η) (hroot : parent.rootsOK roots = true)
    (hc : subcellCurvatureOK c roots maxima weightFloor = true) :
    (∀ j, (weightFloor : ℝ) ≤ parameterWeight a b η j) ∧
    (∀ k i, curvatureBudget criticalQ (fun j => (parameterDJet k ![a,b,η] j).second)
      (fun j l => (parameterHJet k ![a,b,η] j l).second) i ≤ (maxima k i : ℝ)) := by
  have hbound : 0 ≤ parent.η.lo := by
    simp only [ParameterCell.rootsOK, Bool.and_eq_true, decide_eq_true_eq] at hroot
    exact hroot.1
  have hη : 0 ≤ η := (show (0 : ℝ) ≤ parent.η.lo by exact_mod_cast hbound).trans hp.eta.1
  have hR (k j : Fin 3) := ParameterCell.radicalInterval_mem ht hp hroot k j
  simp only [subcellCurvatureOK, subcellCurvatureFromRadicalsOK, radicalIntervalTable, vector_get_ofFn,
    Bool.and_eq_true, List.all_eq_true] at hc
  constructor
  · intro j
    have hm := (parameterWeightInterval_mem ht hη 0 j (hR 0)).1.lower_le (hc.1 j (by simp))
    simpa only [parameterWeightJet_value, Matrix.cons_val] using hm
  · intro k i
    exact (curvatureInterval_mem ht hη k i (hR k)).le_upper (hc.2 k (by simp) i (by simp))

end HlawkaSchatten.BelowExponent.Vertex
