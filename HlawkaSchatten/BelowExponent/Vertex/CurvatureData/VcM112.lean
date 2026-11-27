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

/-! Exact curvature and normalized-weight certificate for vcM112. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcM112Caps : Fin 3 → Fin 3 → ℚ := ![![7737805631/50000000, 6981898163/50000000, 7894248827/100000000], ![5202071451/20000000, 13925851307/50000000, 7978227963/50000000], ![346767639/50000000, 43867691/6250000, 77946167/20000000]]
def vcM112WeightFloor : ℚ := 107524661/100000000
def vcM112Margins : Fin 3 → ℚ := ![4134979/125000000, 333453291/10000000000, 190092609/10000000000]

theorem vcM112_caps_nonneg (k i : Fin 3) : 0 ≤ vcM112Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM112_margin_le (i : Fin 3) : curvatureLoss vcM112Cell vcM112Caps i ≤ vcM112Margins i := by
  fin_cases i <;> decide +kernel

private theorem layer0 : gridLayerCurvatureOK vcM112Cell vcM112Roots 4 4 2 vcM112Caps vcM112WeightFloor 0 = true := by
  replay_curvature_layer

private theorem layer1 : gridLayerCurvatureOK vcM112Cell vcM112Roots 4 4 2 vcM112Caps vcM112WeightFloor 1 = true := by
  replay_curvature_layer

private theorem layer2 : gridLayerCurvatureOK vcM112Cell vcM112Roots 4 4 2 vcM112Caps vcM112WeightFloor 2 = true := by
  replay_curvature_layer

private theorem layer3 : gridLayerCurvatureOK vcM112Cell vcM112Roots 4 4 2 vcM112Caps vcM112WeightFloor 3 = true := by
  replay_curvature_layer

theorem vcM112_grid_layers (i : Fin 4) : gridLayerCurvatureOK vcM112Cell vcM112Roots 4 4 2 vcM112Caps vcM112WeightFloor i = true := by
  fin_cases i
  · exact layer0
  · exact layer1
  · exact layer2
  · exact layer3

end HlawkaSchatten.BelowExponent.Vertex
