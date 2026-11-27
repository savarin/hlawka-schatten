/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck
public import HlawkaSchatten.BelowExponent.Vertex.RootData.VcM112
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.RootData.VcM112

/-! Exact curvature and normalized-weight certificate for vcM113. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcM113Caps : Fin 3 → Fin 3 → ℚ := ![![3301010011/20000000, 930302651/6250000, 83757387/1000000], ![27783432449/100000000, 1859222357/6250000, 8455026561/50000000], ![621919129/100000000, 157291519/25000000, 34750997/10000000]]
def vcM113WeightFloor : ℚ := 3524091/3125000
def vcM113Margins : Fin 3 → ℚ := ![176001109/5000000000, 88689743/2500000000, 50224251/2500000000]

theorem vcM113_caps_nonneg (k i : Fin 3) : 0 ≤ vcM113Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM113_margin_le (i : Fin 3) : curvatureLoss vcM113Cell vcM113Caps i ≤ vcM113Margins i := by
  fin_cases i <;> decide +kernel

private theorem layer0 : gridLayerCurvatureOK vcM113Cell vcM113Roots 4 4 2 vcM113Caps vcM113WeightFloor 0 = true := by
  replay_curvature_layer

private theorem layer1 : gridLayerCurvatureOK vcM113Cell vcM113Roots 4 4 2 vcM113Caps vcM113WeightFloor 1 = true := by
  replay_curvature_layer

private theorem layer2 : gridLayerCurvatureOK vcM113Cell vcM113Roots 4 4 2 vcM113Caps vcM113WeightFloor 2 = true := by
  replay_curvature_layer

private theorem layer3 : gridLayerCurvatureOK vcM113Cell vcM113Roots 4 4 2 vcM113Caps vcM113WeightFloor 3 = true := by
  replay_curvature_layer

theorem vcM113_grid_layers (i : Fin 4) : gridLayerCurvatureOK vcM113Cell vcM113Roots 4 4 2 vcM113Caps vcM113WeightFloor i = true := by
  fin_cases i
  · exact layer0
  · exact layer1
  · exact layer2
  · exact layer3

end HlawkaSchatten.BelowExponent.Vertex
