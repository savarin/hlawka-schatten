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

/-! Exact curvature and normalized-weight certificate for vcM86. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcM86Caps : Fin 3 → Fin 3 → ℚ := ![![20881984217/100000000, 594156217/3125000, 9196116357/100000000], ![1469262843/4000000, 7827476623/20000000, 4987335533/25000000], ![685094651/100000000, 2163849/312500, 42015253/12500000]]
def vcM86WeightFloor : ℚ := 26393679/25000000
def vcM86Margins : Fin 3 → ℚ := ![456713681/10000000000, 460978407/10000000000, 230940813/10000000000]

theorem vcM86_caps_nonneg (k i : Fin 3) : 0 ≤ vcM86Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM86_margin_le (i : Fin 3) : curvatureLoss vcM86Cell vcM86Caps i ≤ vcM86Margins i := by
  fin_cases i <;> decide +kernel

private theorem layer0 : gridLayerCurvatureOK vcM86Cell vcM86Roots 5 5 2 vcM86Caps vcM86WeightFloor 0 = true := by
  replay_curvature_layer

private theorem layer1 : gridLayerCurvatureOK vcM86Cell vcM86Roots 5 5 2 vcM86Caps vcM86WeightFloor 1 = true := by
  replay_curvature_layer

private theorem layer2 : gridLayerCurvatureOK vcM86Cell vcM86Roots 5 5 2 vcM86Caps vcM86WeightFloor 2 = true := by
  replay_curvature_layer

private theorem layer3 : gridLayerCurvatureOK vcM86Cell vcM86Roots 5 5 2 vcM86Caps vcM86WeightFloor 3 = true := by
  replay_curvature_layer

private theorem layer4 : gridLayerCurvatureOK vcM86Cell vcM86Roots 5 5 2 vcM86Caps vcM86WeightFloor 4 = true := by
  replay_curvature_layer

theorem vcM86_grid_layers (i : Fin 5) : gridLayerCurvatureOK vcM86Cell vcM86Roots 5 5 2 vcM86Caps vcM86WeightFloor i = true := by
  fin_cases i
  · exact layer0
  · exact layer1
  · exact layer2
  · exact layer3
  · exact layer4

end HlawkaSchatten.BelowExponent.Vertex
