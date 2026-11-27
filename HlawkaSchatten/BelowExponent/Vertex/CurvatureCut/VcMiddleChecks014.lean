/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs192
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs224
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs192
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs224

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem vcM29Child4Cut_layer1 : gridLayerCurvatureOK
    vcM29Child4CutCell vcM29Child4CutRoots 2 2 1 vcM29Child4CutCaps vcM29Child4CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM29Child5Cut_layer0 : gridLayerCurvatureOK
    vcM29Child5CutCell vcM29Child5CutRoots 2 2 1 vcM29Child5CutCaps vcM29Child5CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM29Child5Cut_layer1 : gridLayerCurvatureOK
    vcM29Child5CutCell vcM29Child5CutRoots 2 2 1 vcM29Child5CutCaps vcM29Child5CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM29Child6Cut_layer0 : gridLayerCurvatureOK
    vcM29Child6CutCell vcM29Child6CutRoots 1 1 1 vcM29Child6CutCaps vcM29Child6CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM29Child7Cut_layer0 : gridLayerCurvatureOK
    vcM29Child7CutCell vcM29Child7CutRoots 1 1 1 vcM29Child7CutCaps vcM29Child7CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM31Child0Cut_layer0 : gridLayerCurvatureOK
    vcM31Child0CutCell vcM31Child0CutRoots 1 1 1 vcM31Child0CutCaps vcM31Child0CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM31Child1Cut_layer0 : gridLayerCurvatureOK
    vcM31Child1CutCell vcM31Child1CutRoots 1 1 1 vcM31Child1CutCaps vcM31Child1CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM31Child2Cut_layer0 : gridLayerCurvatureOK
    vcM31Child2CutCell vcM31Child2CutRoots 1 1 1 vcM31Child2CutCaps vcM31Child2CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM31Child3Cut_layer0 : gridLayerCurvatureOK
    vcM31Child3CutCell vcM31Child3CutRoots 1 1 1 vcM31Child3CutCaps vcM31Child3CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM31Child4Cut_layer0 : gridLayerCurvatureOK
    vcM31Child4CutCell vcM31Child4CutRoots 1 1 1 vcM31Child4CutCaps vcM31Child4CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM31Child5Cut_layer0 : gridLayerCurvatureOK
    vcM31Child5CutCell vcM31Child5CutRoots 1 1 1 vcM31Child5CutCaps vcM31Child5CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM31Child6Cut_layer0 : gridLayerCurvatureOK
    vcM31Child6CutCell vcM31Child6CutRoots 1 1 1 vcM31Child6CutCaps vcM31Child6CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM31Child7Cut_layer0 : gridLayerCurvatureOK
    vcM31Child7CutCell vcM31Child7CutRoots 1 1 1 vcM31Child7CutCaps vcM31Child7CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM59Child0Cut_layer0 : gridLayerCurvatureOK
    vcM59Child0CutCell vcM59Child0CutRoots 2 2 1 vcM59Child0CutCaps vcM59Child0CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM59Child0Cut_layer1 : gridLayerCurvatureOK
    vcM59Child0CutCell vcM59Child0CutRoots 2 2 1 vcM59Child0CutCaps vcM59Child0CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM59Child1Cut_layer0 : gridLayerCurvatureOK
    vcM59Child1CutCell vcM59Child1CutRoots 2 2 1 vcM59Child1CutCaps vcM59Child1CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM59Child1Cut_layer1 : gridLayerCurvatureOK
    vcM59Child1CutCell vcM59Child1CutRoots 2 2 1 vcM59Child1CutCaps vcM59Child1CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM59Child2Cut_layer0 : gridLayerCurvatureOK
    vcM59Child2CutCell vcM59Child2CutRoots 1 1 1 vcM59Child2CutCaps vcM59Child2CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM59Child3Cut_layer0 : gridLayerCurvatureOK
    vcM59Child3CutCell vcM59Child3CutRoots 1 1 1 vcM59Child3CutCaps vcM59Child3CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM59Child4Cut_layer0 : gridLayerCurvatureOK
    vcM59Child4CutCell vcM59Child4CutRoots 2 2 1 vcM59Child4CutCaps vcM59Child4CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM59Child4Cut_layer1 : gridLayerCurvatureOK
    vcM59Child4CutCell vcM59Child4CutRoots 2 2 1 vcM59Child4CutCaps vcM59Child4CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM59Child5Cut_layer0 : gridLayerCurvatureOK
    vcM59Child5CutCell vcM59Child5CutRoots 2 2 1 vcM59Child5CutCaps vcM59Child5CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
