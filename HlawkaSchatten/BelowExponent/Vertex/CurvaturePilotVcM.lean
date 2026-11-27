/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvaturePilotData
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.RootData.VcM000

/-! The six first-coordinate layers of the closed VC-M pilot. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private theorem layer0 : gridLayerCurvatureOK vcM0Cell vcM0Roots 6 6 2 vcM0Caps vcM0WeightFloor 0 = true := by
  replay_curvature_layer

private theorem layer1 : gridLayerCurvatureOK vcM0Cell vcM0Roots 6 6 2 vcM0Caps vcM0WeightFloor 1 = true := by
  replay_curvature_layer

private theorem layer2 : gridLayerCurvatureOK vcM0Cell vcM0Roots 6 6 2 vcM0Caps vcM0WeightFloor 2 = true := by
  replay_curvature_layer

private theorem layer3 : gridLayerCurvatureOK vcM0Cell vcM0Roots 6 6 2 vcM0Caps vcM0WeightFloor 3 = true := by
  replay_curvature_layer

private theorem layer4 : gridLayerCurvatureOK vcM0Cell vcM0Roots 6 6 2 vcM0Caps vcM0WeightFloor 4 = true := by
  replay_curvature_layer

private theorem layer5 : gridLayerCurvatureOK vcM0Cell vcM0Roots 6 6 2 vcM0Caps vcM0WeightFloor 5 = true := by
  replay_curvature_layer

theorem vcM0_grid_layers (i : Fin 6) : gridLayerCurvatureOK vcM0Cell vcM0Roots 6 6 2 vcM0Caps vcM0WeightFloor i = true := by
  fin_cases i
  · exact layer0
  · exact layer1
  · exact layer2
  · exact layer3
  · exact layer4
  · exact layer5

end HlawkaSchatten.BelowExponent.Vertex
