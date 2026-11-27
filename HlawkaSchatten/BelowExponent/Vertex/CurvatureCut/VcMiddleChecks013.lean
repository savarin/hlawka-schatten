/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs192
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs192

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem vcM1Child2Cut_layer0 : gridLayerCurvatureOK
    vcM1Child2CutCell vcM1Child2CutRoots 1 1 1 vcM1Child2CutCaps vcM1Child2CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM1Child3Cut_layer0 : gridLayerCurvatureOK
    vcM1Child3CutCell vcM1Child3CutRoots 1 1 1 vcM1Child3CutCaps vcM1Child3CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM1Child4Cut_layer0 : gridLayerCurvatureOK
    vcM1Child4CutCell vcM1Child4CutRoots 1 1 1 vcM1Child4CutCaps vcM1Child4CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM1Child5Cut_layer0 : gridLayerCurvatureOK
    vcM1Child5CutCell vcM1Child5CutRoots 1 1 1 vcM1Child5CutCaps vcM1Child5CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM1Child6Cut_layer0 : gridLayerCurvatureOK
    vcM1Child6CutCell vcM1Child6CutRoots 1 1 1 vcM1Child6CutCaps vcM1Child6CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM1Child7Cut_layer0 : gridLayerCurvatureOK
    vcM1Child7CutCell vcM1Child7CutRoots 1 1 1 vcM1Child7CutCaps vcM1Child7CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM28Child0Cut_layer0 : gridLayerCurvatureOK
    vcM28Child0CutCell vcM28Child0CutRoots 1 1 1 vcM28Child0CutCaps vcM28Child0CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM28Child1Cut_layer0 : gridLayerCurvatureOK
    vcM28Child1CutCell vcM28Child1CutRoots 2 2 1 vcM28Child1CutCaps vcM28Child1CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM28Child1Cut_layer1 : gridLayerCurvatureOK
    vcM28Child1CutCell vcM28Child1CutRoots 2 2 1 vcM28Child1CutCaps vcM28Child1CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM28Child2Cut_layer0 : gridLayerCurvatureOK
    vcM28Child2CutCell vcM28Child2CutRoots 1 1 1 vcM28Child2CutCaps vcM28Child2CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM28Child3Cut_layer0 : gridLayerCurvatureOK
    vcM28Child3CutCell vcM28Child3CutRoots 1 1 1 vcM28Child3CutCaps vcM28Child3CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM28Child4Cut_layer0 : gridLayerCurvatureOK
    vcM28Child4CutCell vcM28Child4CutRoots 1 1 1 vcM28Child4CutCaps vcM28Child4CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM28Child5Cut_layer0 : gridLayerCurvatureOK
    vcM28Child5CutCell vcM28Child5CutRoots 2 2 1 vcM28Child5CutCaps vcM28Child5CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM28Child5Cut_layer1 : gridLayerCurvatureOK
    vcM28Child5CutCell vcM28Child5CutRoots 2 2 1 vcM28Child5CutCaps vcM28Child5CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM28Child6Cut_layer0 : gridLayerCurvatureOK
    vcM28Child6CutCell vcM28Child6CutRoots 1 1 1 vcM28Child6CutCaps vcM28Child6CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM28Child7Cut_layer0 : gridLayerCurvatureOK
    vcM28Child7CutCell vcM28Child7CutRoots 1 1 1 vcM28Child7CutCaps vcM28Child7CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM29Child0Cut_layer0 : gridLayerCurvatureOK
    vcM29Child0CutCell vcM29Child0CutRoots 2 2 1 vcM29Child0CutCaps vcM29Child0CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM29Child0Cut_layer1 : gridLayerCurvatureOK
    vcM29Child0CutCell vcM29Child0CutRoots 2 2 1 vcM29Child0CutCaps vcM29Child0CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM29Child1Cut_layer0 : gridLayerCurvatureOK
    vcM29Child1CutCell vcM29Child1CutRoots 2 2 1 vcM29Child1CutCaps vcM29Child1CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM29Child1Cut_layer1 : gridLayerCurvatureOK
    vcM29Child1CutCell vcM29Child1CutRoots 2 2 1 vcM29Child1CutCaps vcM29Child1CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM29Child2Cut_layer0 : gridLayerCurvatureOK
    vcM29Child2CutCell vcM29Child2CutRoots 1 1 1 vcM29Child2CutCaps vcM29Child2CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM29Child3Cut_layer0 : gridLayerCurvatureOK
    vcM29Child3CutCell vcM29Child3CutRoots 1 1 1 vcM29Child3CutCaps vcM29Child3CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM29Child4Cut_layer0 : gridLayerCurvatureOK
    vcM29Child4CutCell vcM29Child4CutRoots 2 2 1 vcM29Child4CutCaps vcM29Child4CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
