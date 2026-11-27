/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureIntervals
public import HlawkaSchatten.BelowExponent.Vertex.ParameterGrid

/-! Parent curvature and weight inequalities from a closed grid of checked subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

theorem gridCurvatureOK_of_layers {c : ParameterCell} {roots : Fin 3 → RatBounds} {na nb nη : ℕ}
    {maxima : Fin 3 → Fin 3 → ℚ} {weightFloor : ℚ}
    (h : ∀ i, gridLayerCurvatureOK c roots na nb nη maxima weightFloor i = true) :
    gridCurvatureOK c roots na nb nη maxima weightFloor = true := by
  simp only [gridCurvatureOK, ParameterCell.grid, List.all_flatMap, List.all_map, Function.comp_apply,
    List.all_eq_true]
  intro i _ j _ k _
  have hi := h i
  simp only [gridLayerCurvatureOK, List.all_eq_true] at hi
  exact hi j (by simp) k (by simp)

theorem gridCurvatureOK_sound {c : ParameterCell} {roots : Fin 3 → RatBounds} {na nb nη : ℕ}
    {maxima : Fin 3 → Fin 3 → ℚ} {weightFloor : ℚ} {a b η : ℝ} (ht : c.Contains a b η)
    (ha : 0 < na) (hb : 0 < nb) (hη : 0 < nη) (hroot : c.rootsOK roots = true)
    (hc : gridCurvatureOK c roots na nb nη maxima weightFloor = true) :
    (∀ j, (weightFloor : ℝ) ≤ parameterWeight a b η j) ∧
    (∀ k i, curvatureBudget criticalQ (fun j => (parameterDJet k ![a,b,η] j).second)
      (fun j l => (parameterHJet k ![a,b,η] j l).second) i ≤ (maxima k i : ℝ)) := by
  obtain ⟨d, hd, hx⟩ := ParameterCell.grid_cover ht ha hb hη
  exact subcellCurvatureOK_sound hx ht hroot (List.all_eq_true.mp hc d hd)

end HlawkaSchatten.BelowExponent.Vertex
