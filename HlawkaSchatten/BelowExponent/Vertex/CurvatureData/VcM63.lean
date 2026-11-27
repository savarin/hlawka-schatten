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

/-! Exact curvature and normalized-weight certificate for vcM63. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcM63Caps : Fin 3 → Fin 3 → ℚ := ![![2514935941/12500000, 17060443613/100000000, 1040344453/12500000], ![10882041863/50000000, 22905171007/100000000, 11186165631/100000000], ![80309477/12500000, 82351733/12500000, 80056821/25000000]]
def vcM63WeightFloor : ℚ := 110524713/100000000
def vcM63Margins : Fin 3 → ℚ := ![8335303/250000000, 63717133/2000000000, 7775103/500000000]

theorem vcM63_caps_nonneg (k i : Fin 3) : 0 ≤ vcM63Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM63_margin_le (i : Fin 3) : curvatureLoss vcM63Cell vcM63Caps i ≤ vcM63Margins i := by
  fin_cases i <;> decide +kernel

private theorem layer0 : gridLayerCurvatureOK vcM63Cell vcM63Roots 4 4 2 vcM63Caps vcM63WeightFloor 0 = true := by
  replay_curvature_layer

private theorem layer1 : gridLayerCurvatureOK vcM63Cell vcM63Roots 4 4 2 vcM63Caps vcM63WeightFloor 1 = true := by
  replay_curvature_layer

private theorem layer2 : gridLayerCurvatureOK vcM63Cell vcM63Roots 4 4 2 vcM63Caps vcM63WeightFloor 2 = true := by
  replay_curvature_layer

private theorem layer3 : gridLayerCurvatureOK vcM63Cell vcM63Roots 4 4 2 vcM63Caps vcM63WeightFloor 3 = true := by
  replay_curvature_layer

theorem vcM63_grid_layers (i : Fin 4) : gridLayerCurvatureOK vcM63Cell vcM63Roots 4 4 2 vcM63Caps vcM63WeightFloor i = true := by
  fin_cases i
  · exact layer0
  · exact layer1
  · exact layer2
  · exact layer3

end HlawkaSchatten.BelowExponent.Vertex
