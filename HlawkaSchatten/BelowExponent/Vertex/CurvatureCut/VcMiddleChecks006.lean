/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs000
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs032
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs000
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs032

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem vcM33Cut_layer1 : gridLayerCurvatureOK
    vcM33CutCell vcM33CutRoots 4 4 2 vcM33CutCaps vcM33CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM33Cut_layer2 : gridLayerCurvatureOK
    vcM33CutCell vcM33CutRoots 4 4 2 vcM33CutCaps vcM33CutWeightFloor 2 = true := by
  replay_curvature_layer

theorem vcM33Cut_layer3 : gridLayerCurvatureOK
    vcM33CutCell vcM33CutRoots 4 4 2 vcM33CutCaps vcM33CutWeightFloor 3 = true := by
  replay_curvature_layer

theorem vcM34Cut_layer0 : gridLayerCurvatureOK
    vcM34CutCell vcM34CutRoots 1 1 1 vcM34CutCaps vcM34CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM35Cut_layer0 : gridLayerCurvatureOK
    vcM35CutCell vcM35CutRoots 2 2 1 vcM35CutCaps vcM35CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM35Cut_layer1 : gridLayerCurvatureOK
    vcM35CutCell vcM35CutRoots 2 2 1 vcM35CutCaps vcM35CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM36Cut_layer0 : gridLayerCurvatureOK
    vcM36CutCell vcM36CutRoots 1 1 1 vcM36CutCaps vcM36CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM37Cut_layer0 : gridLayerCurvatureOK
    vcM37CutCell vcM37CutRoots 1 1 1 vcM37CutCaps vcM37CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM38Cut_layer0 : gridLayerCurvatureOK
    vcM38CutCell vcM38CutRoots 1 1 1 vcM38CutCaps vcM38CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
