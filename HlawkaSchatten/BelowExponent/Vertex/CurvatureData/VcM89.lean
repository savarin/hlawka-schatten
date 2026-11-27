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

/-! Exact curvature and normalized-weight certificate for vcM89. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcM89Caps : Fin 3 → Fin 3 → ℚ := ![![18402428193/100000000, 201620607/1250000, 8422469203/100000000], ![6253978849/25000000, 26479268749/100000000, 3528824891/25000000], ![632577509/100000000, 160507471/25000000, 1671171/500000]]
def vcM89WeightFloor : ℚ := 27902863/25000000
def vcM89Margins : Fin 3 → ℚ := ![345307059/10000000000, 67814917/2000000000, 44825007/2500000000]

theorem vcM89_caps_nonneg (k i : Fin 3) : 0 ≤ vcM89Caps k i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem vcM89_margin_le (i : Fin 3) : curvatureLoss vcM89Cell vcM89Caps i ≤ vcM89Margins i := by
  fin_cases i <;> decide +kernel

private theorem layer0 : gridLayerCurvatureOK vcM89Cell vcM89Roots 4 4 2 vcM89Caps vcM89WeightFloor 0 = true := by
  replay_curvature_layer

private theorem layer1 : gridLayerCurvatureOK vcM89Cell vcM89Roots 4 4 2 vcM89Caps vcM89WeightFloor 1 = true := by
  replay_curvature_layer

private theorem layer2 : gridLayerCurvatureOK vcM89Cell vcM89Roots 4 4 2 vcM89Caps vcM89WeightFloor 2 = true := by
  replay_curvature_layer

private theorem layer3 : gridLayerCurvatureOK vcM89Cell vcM89Roots 4 4 2 vcM89Caps vcM89WeightFloor 3 = true := by
  replay_curvature_layer

theorem vcM89_grid_layers (i : Fin 4) : gridLayerCurvatureOK vcM89Cell vcM89Roots 4 4 2 vcM89Caps vcM89WeightFloor i = true := by
  fin_cases i
  · exact layer0
  · exact layer1
  · exact layer2
  · exact layer3

end HlawkaSchatten.BelowExponent.Vertex
