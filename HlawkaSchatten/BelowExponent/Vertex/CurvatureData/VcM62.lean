/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck
public import HlawkaSchatten.BelowExponent.Vertex.RootData.VcM048
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.RootData.VcM048

/-! Exact curvature and normalized-weight certificate for vcM62. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcM62Caps : Fin 3 → Fin 3 → ℚ := ![![18950762273/100000000, 16035392363/100000000, 3929648487/50000000], ![20432995811/100000000, 2687532723/12500000, 10580533329/100000000], ![358521101/50000000, 737016471/100000000, 44953837/12500000]]
def vcM62WeightFloor : ℚ := 105261431/100000000
def vcM62Margins : Fin 3 → ℚ := ![314601527/10000000000, 75088967/2500000000, 29505967/2000000000]

theorem vcM62_caps_nonneg (k i : Fin 3) : 0 ≤ vcM62Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM62_margin_le (i : Fin 3) : curvatureLoss vcM62Cell vcM62Caps i ≤ vcM62Margins i := by
  fin_cases i <;> decide +kernel

private theorem layer0 : gridLayerCurvatureOK vcM62Cell vcM62Roots 4 4 2 vcM62Caps vcM62WeightFloor 0 = true := by
  replay_curvature_layer

private theorem layer1 : gridLayerCurvatureOK vcM62Cell vcM62Roots 4 4 2 vcM62Caps vcM62WeightFloor 1 = true := by
  replay_curvature_layer

private theorem layer2 : gridLayerCurvatureOK vcM62Cell vcM62Roots 4 4 2 vcM62Caps vcM62WeightFloor 2 = true := by
  replay_curvature_layer

private theorem layer3 : gridLayerCurvatureOK vcM62Cell vcM62Roots 4 4 2 vcM62Caps vcM62WeightFloor 3 = true := by
  replay_curvature_layer

theorem vcM62_grid_layers (i : Fin 4) : gridLayerCurvatureOK vcM62Cell vcM62Roots 4 4 2 vcM62Caps vcM62WeightFloor i = true := by
  fin_cases i
  · exact layer0
  · exact layer1
  · exact layer2
  · exact layer3

end HlawkaSchatten.BelowExponent.Vertex
