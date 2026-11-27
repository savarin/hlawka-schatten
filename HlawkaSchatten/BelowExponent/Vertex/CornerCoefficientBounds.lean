/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CoefficientIntervals

/-! The value fields of the checked jets supply the coefficients for a vertex corner. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

theorem ParameterCell.coefficientValues_mem {c parent : ParameterCell} {roots : Fin 3 → RatBounds}
    {a b η : ℝ} (hc : c.Contains a b η) (hp : parent.Contains a b η)
    (hroot : parent.rootsOK roots = true) :
    let v := axisCoefficientIntervals c roots 0
    (∀ j, (v.d.get j).value.Contains (parameterD a b η j)) ∧
    (∀ j, (v.weight.get j).value.Contains (parameterWeight a b η j)) ∧
    (∀ i j, ((v.h.get i).get j).value.Contains
      ((1 - parameterDirection a b i) * parameterWeight a b η j)) := by
  have hlo : 0 ≤ parent.η.lo := by
    simp only [ParameterCell.rootsOK, Bool.and_eq_true, decide_eq_true_eq] at hroot
    exact hroot.1
  have hη : 0 ≤ η := (show (0 : ℝ) ≤ parent.η.lo by exact_mod_cast hlo).trans hp.eta.1
  have hR (j : Fin 3) := ParameterCell.radicalInterval_mem hc hp hroot 0 j
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simpa only [parameterDJet_value, Matrix.cons_val] using (parameterDInterval_mem hc hη 0 j hR).1
  · intro j
    simpa only [parameterWeightJet_value, Matrix.cons_val] using (parameterWeightInterval_mem hc hη 0 j hR).1
  · intro i j
    simpa only [parameterHJet_value, Matrix.cons_val] using (parameterHInterval_mem hc hη 0 i j hR).1

end HlawkaSchatten.BelowExponent.Vertex
