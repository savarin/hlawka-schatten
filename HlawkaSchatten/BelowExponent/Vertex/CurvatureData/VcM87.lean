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

/-! Exact curvature and normalized-weight certificate for vcM87. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcM87Caps : Fin 3 → Fin 3 → ℚ := ![![8350422501/50000000, 15113862107/100000000, 248077411/4000000], ![26314618987/100000000, 7118319327/25000000, 13202365869/100000000], ![3868051/781250, 62385699/12500000, 248113511/100000000]]
def vcM87WeightFloor : ℚ := 22344253/20000000
def vcM87Margins : Fin 3 → ℚ := ![68166737/2000000000, 345338239/10000000000, 153989173/10000000000]

theorem vcM87_caps_nonneg (k i : Fin 3) : 0 ≤ vcM87Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM87_margin_le (i : Fin 3) : curvatureLoss vcM87Cell vcM87Caps i ≤ vcM87Margins i := by
  fin_cases i <;> decide +kernel

private theorem layer0 : gridLayerCurvatureOK vcM87Cell vcM87Roots 8 8 2 vcM87Caps vcM87WeightFloor 0 = true := by
  replay_curvature_layer

private theorem layer1 : gridLayerCurvatureOK vcM87Cell vcM87Roots 8 8 2 vcM87Caps vcM87WeightFloor 1 = true := by
  replay_curvature_layer

private theorem layer2 : gridLayerCurvatureOK vcM87Cell vcM87Roots 8 8 2 vcM87Caps vcM87WeightFloor 2 = true := by
  replay_curvature_layer

private theorem layer3 : gridLayerCurvatureOK vcM87Cell vcM87Roots 8 8 2 vcM87Caps vcM87WeightFloor 3 = true := by
  replay_curvature_layer

private theorem layer4 : gridLayerCurvatureOK vcM87Cell vcM87Roots 8 8 2 vcM87Caps vcM87WeightFloor 4 = true := by
  replay_curvature_layer

private theorem layer5 : gridLayerCurvatureOK vcM87Cell vcM87Roots 8 8 2 vcM87Caps vcM87WeightFloor 5 = true := by
  replay_curvature_layer

private theorem layer6 : gridLayerCurvatureOK vcM87Cell vcM87Roots 8 8 2 vcM87Caps vcM87WeightFloor 6 = true := by
  replay_curvature_layer

private theorem layer7 : gridLayerCurvatureOK vcM87Cell vcM87Roots 8 8 2 vcM87Caps vcM87WeightFloor 7 = true := by
  replay_curvature_layer

theorem vcM87_grid_layers (i : Fin 8) : gridLayerCurvatureOK vcM87Cell vcM87Roots 8 8 2 vcM87Caps vcM87WeightFloor i = true := by
  fin_cases i
  · exact layer0
  · exact layer1
  · exact layer2
  · exact layer3
  · exact layer4
  · exact layer5
  · exact layer6
  · exact layer7

end HlawkaSchatten.BelowExponent.Vertex
