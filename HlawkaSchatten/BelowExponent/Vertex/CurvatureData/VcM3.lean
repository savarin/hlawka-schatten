/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck
public import HlawkaSchatten.BelowExponent.Vertex.RootData.VcM000
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.RootData.VcM000

/-! Exact curvature and normalized-weight certificate for vcM3. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcM3Caps : Fin 3 → Fin 3 → ℚ := ![![6105574849/25000000, 4926308079/25000000, 7350984177/100000000], ![326540407/2000000, 860566533/5000000, 1212289029/20000000], ![654542757/100000000, 349187081/50000000, 147361427/50000000]]
def vcM3WeightFloor : ℚ := 108576391/100000000
def vcM3Margins : Fin 3 → ℚ := ![162333583/5000000000, 295146511/10000000000, 4305089/400000000]

theorem vcM3_caps_nonneg (k i : Fin 3) : 0 ≤ vcM3Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM3_margin_le (i : Fin 3) : curvatureLoss vcM3Cell vcM3Caps i ≤ vcM3Margins i := by
  fin_cases i <;> decide +kernel

private theorem layer0 : gridLayerCurvatureOK vcM3Cell vcM3Roots 4 4 2 vcM3Caps vcM3WeightFloor 0 = true := by
  replay_curvature_layer

private theorem layer1 : gridLayerCurvatureOK vcM3Cell vcM3Roots 4 4 2 vcM3Caps vcM3WeightFloor 1 = true := by
  replay_curvature_layer

private theorem layer2 : gridLayerCurvatureOK vcM3Cell vcM3Roots 4 4 2 vcM3Caps vcM3WeightFloor 2 = true := by
  replay_curvature_layer

private theorem layer3 : gridLayerCurvatureOK vcM3Cell vcM3Roots 4 4 2 vcM3Caps vcM3WeightFloor 3 = true := by
  replay_curvature_layer

theorem vcM3_grid_layers (i : Fin 4) : gridLayerCurvatureOK vcM3Cell vcM3Roots 4 4 2 vcM3Caps vcM3WeightFloor i = true := by
  fin_cases i
  · exact layer0
  · exact layer1
  · exact layer2
  · exact layer3

end HlawkaSchatten.BelowExponent.Vertex
