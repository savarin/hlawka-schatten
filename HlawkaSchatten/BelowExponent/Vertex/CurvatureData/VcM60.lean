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

/-! Exact curvature and normalized-weight certificate for vcM60. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcM60Caps : Fin 3 → Fin 3 → ℚ := ![![11948522839/50000000, 10571272983/50000000, 1162121269/12500000], ![6515759389/20000000, 4289931307/12500000, 2017771823/12500000], ![174663169/25000000, 142917181/20000000, 5041333/1562500]]
def vcM60WeightFloor : ℚ := 104451143/100000000
def vcM60Margins : Fin 3 → ℚ := ![447956069/10000000000, 440189073/10000000000, 201855253/10000000000]

theorem vcM60_caps_nonneg (k i : Fin 3) : 0 ≤ vcM60Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM60_margin_le (i : Fin 3) : curvatureLoss vcM60Cell vcM60Caps i ≤ vcM60Margins i := by
  fin_cases i <;> decide +kernel

private theorem layer0 : gridLayerCurvatureOK vcM60Cell vcM60Roots 5 5 2 vcM60Caps vcM60WeightFloor 0 = true := by
  replay_curvature_layer

private theorem layer1 : gridLayerCurvatureOK vcM60Cell vcM60Roots 5 5 2 vcM60Caps vcM60WeightFloor 1 = true := by
  replay_curvature_layer

private theorem layer2 : gridLayerCurvatureOK vcM60Cell vcM60Roots 5 5 2 vcM60Caps vcM60WeightFloor 2 = true := by
  replay_curvature_layer

private theorem layer3 : gridLayerCurvatureOK vcM60Cell vcM60Roots 5 5 2 vcM60Caps vcM60WeightFloor 3 = true := by
  replay_curvature_layer

private theorem layer4 : gridLayerCurvatureOK vcM60Cell vcM60Roots 5 5 2 vcM60Caps vcM60WeightFloor 4 = true := by
  replay_curvature_layer

theorem vcM60_grid_layers (i : Fin 5) : gridLayerCurvatureOK vcM60Cell vcM60Roots 5 5 2 vcM60Caps vcM60WeightFloor i = true := by
  fin_cases i
  · exact layer0
  · exact layer1
  · exact layer2
  · exact layer3
  · exact layer4

end HlawkaSchatten.BelowExponent.Vertex
