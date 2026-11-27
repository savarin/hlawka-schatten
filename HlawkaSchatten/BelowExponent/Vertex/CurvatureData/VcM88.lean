/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck
public import HlawkaSchatten.BelowExponent.Vertex.RootData.VcM080
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.RootData.VcM080

/-! Exact curvature and normalized-weight certificate for vcM88. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcM88Caps : Fin 3 → Fin 3 → ℚ := ![![4321945859/25000000, 7571888257/50000000, 992889363/12500000], ![11722561437/50000000, 12407800229/50000000, 666702037/5000000], ![44103483/6250000, 7171633/1000000, 375037363/100000000]]
def vcM88WeightFloor : ℚ := 106357233/100000000
def vcM88Margins : Fin 3 → ℚ := ![81257981/2500000000, 319099717/10000000000, 169845037/10000000000]

theorem vcM88_caps_nonneg (k i : Fin 3) : 0 ≤ vcM88Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM88_margin_le (i : Fin 3) : curvatureLoss vcM88Cell vcM88Caps i ≤ vcM88Margins i := by
  fin_cases i <;> decide +kernel

private theorem layer0 : gridLayerCurvatureOK vcM88Cell vcM88Roots 4 4 2 vcM88Caps vcM88WeightFloor 0 = true := by
  replay_curvature_layer

private theorem layer1 : gridLayerCurvatureOK vcM88Cell vcM88Roots 4 4 2 vcM88Caps vcM88WeightFloor 1 = true := by
  replay_curvature_layer

private theorem layer2 : gridLayerCurvatureOK vcM88Cell vcM88Roots 4 4 2 vcM88Caps vcM88WeightFloor 2 = true := by
  replay_curvature_layer

private theorem layer3 : gridLayerCurvatureOK vcM88Cell vcM88Roots 4 4 2 vcM88Caps vcM88WeightFloor 3 = true := by
  replay_curvature_layer

theorem vcM88_grid_layers (i : Fin 4) : gridLayerCurvatureOK vcM88Cell vcM88Roots 4 4 2 vcM88Caps vcM88WeightFloor i = true := by
  fin_cases i
  · exact layer0
  · exact layer1
  · exact layer2
  · exact layer3

end HlawkaSchatten.BelowExponent.Vertex
