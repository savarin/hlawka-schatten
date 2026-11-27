/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs224
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs224

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem vcM59Child5Cut_layer1 : gridLayerCurvatureOK
    vcM59Child5CutCell vcM59Child5CutRoots 2 2 1 vcM59Child5CutCaps vcM59Child5CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM59Child6Cut_layer0 : gridLayerCurvatureOK
    vcM59Child6CutCell vcM59Child6CutRoots 1 1 1 vcM59Child6CutCaps vcM59Child6CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM59Child7Cut_layer0 : gridLayerCurvatureOK
    vcM59Child7CutCell vcM59Child7CutRoots 1 1 1 vcM59Child7CutCaps vcM59Child7CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM61Child0Cut_layer0 : gridLayerCurvatureOK
    vcM61Child0CutCell vcM61Child0CutRoots 1 1 1 vcM61Child0CutCaps vcM61Child0CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM61Child1Cut_layer0 : gridLayerCurvatureOK
    vcM61Child1CutCell vcM61Child1CutRoots 1 1 1 vcM61Child1CutCaps vcM61Child1CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM61Child2Cut_layer0 : gridLayerCurvatureOK
    vcM61Child2CutCell vcM61Child2CutRoots 1 1 1 vcM61Child2CutCaps vcM61Child2CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM61Child3Cut_layer0 : gridLayerCurvatureOK
    vcM61Child3CutCell vcM61Child3CutRoots 1 1 1 vcM61Child3CutCaps vcM61Child3CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM61Child4Cut_layer0 : gridLayerCurvatureOK
    vcM61Child4CutCell vcM61Child4CutRoots 1 1 1 vcM61Child4CutCaps vcM61Child4CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM61Child5Cut_layer0 : gridLayerCurvatureOK
    vcM61Child5CutCell vcM61Child5CutRoots 1 1 1 vcM61Child5CutCaps vcM61Child5CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM61Child6Cut_layer0 : gridLayerCurvatureOK
    vcM61Child6CutCell vcM61Child6CutRoots 1 1 1 vcM61Child6CutCaps vcM61Child6CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM61Child7Cut_layer0 : gridLayerCurvatureOK
    vcM61Child7CutCell vcM61Child7CutRoots 1 1 1 vcM61Child7CutCaps vcM61Child7CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
