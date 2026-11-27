/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs032
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs064
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs032
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs064

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem vcM71Cut_layer0 : gridLayerCurvatureOK
    vcM71CutCell vcM71CutRoots 1 1 1 vcM71CutCaps vcM71CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM72Cut_layer0 : gridLayerCurvatureOK
    vcM72CutCell vcM72CutRoots 1 1 1 vcM72CutCaps vcM72CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM73Cut_layer0 : gridLayerCurvatureOK
    vcM73CutCell vcM73CutRoots 1 1 1 vcM73CutCaps vcM73CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM74Cut_layer0 : gridLayerCurvatureOK
    vcM74CutCell vcM74CutRoots 1 1 1 vcM74CutCaps vcM74CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM75Cut_layer0 : gridLayerCurvatureOK
    vcM75CutCell vcM75CutRoots 1 1 1 vcM75CutCaps vcM75CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM76Cut_layer0 : gridLayerCurvatureOK
    vcM76CutCell vcM76CutRoots 1 1 1 vcM76CutCaps vcM76CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM77Cut_layer0 : gridLayerCurvatureOK
    vcM77CutCell vcM77CutRoots 1 1 1 vcM77CutCaps vcM77CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM78Cut_layer0 : gridLayerCurvatureOK
    vcM78CutCell vcM78CutRoots 1 1 1 vcM78CutCaps vcM78CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM79Cut_layer0 : gridLayerCurvatureOK
    vcM79CutCell vcM79CutRoots 1 1 1 vcM79CutCaps vcM79CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM80Cut_layer0 : gridLayerCurvatureOK
    vcM80CutCell vcM80CutRoots 1 1 1 vcM80CutCaps vcM80CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM81Cut_layer0 : gridLayerCurvatureOK
    vcM81CutCell vcM81CutRoots 1 1 1 vcM81CutCaps vcM81CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM82Cut_layer0 : gridLayerCurvatureOK
    vcM82CutCell vcM82CutRoots 1 1 1 vcM82CutCaps vcM82CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM83Cut_layer0 : gridLayerCurvatureOK
    vcM83CutCell vcM83CutRoots 1 1 1 vcM83CutCaps vcM83CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM84Cut_layer0 : gridLayerCurvatureOK
    vcM84CutCell vcM84CutRoots 1 1 1 vcM84CutCaps vcM84CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM85Cut_layer0 : gridLayerCurvatureOK
    vcM85CutCell vcM85CutRoots 1 1 1 vcM85CutCaps vcM85CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM90Cut_layer0 : gridLayerCurvatureOK
    vcM90CutCell vcM90CutRoots 2 2 1 vcM90CutCaps vcM90CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM90Cut_layer1 : gridLayerCurvatureOK
    vcM90CutCell vcM90CutRoots 2 2 1 vcM90CutCaps vcM90CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM91Cut_layer0 : gridLayerCurvatureOK
    vcM91CutCell vcM91CutRoots 2 2 1 vcM91CutCaps vcM91CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM91Cut_layer1 : gridLayerCurvatureOK
    vcM91CutCell vcM91CutRoots 2 2 1 vcM91CutCaps vcM91CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM92Cut_layer0 : gridLayerCurvatureOK
    vcM92CutCell vcM92CutRoots 1 1 1 vcM92CutCaps vcM92CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM93Cut_layer0 : gridLayerCurvatureOK
    vcM93CutCell vcM93CutRoots 1 1 1 vcM93CutCaps vcM93CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM94Cut_layer0 : gridLayerCurvatureOK
    vcM94CutCell vcM94CutRoots 1 1 1 vcM94CutCaps vcM94CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM95Cut_layer0 : gridLayerCurvatureOK
    vcM95CutCell vcM95CutRoots 1 1 1 vcM95CutCaps vcM95CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM96Cut_layer0 : gridLayerCurvatureOK
    vcM96CutCell vcM96CutRoots 1 1 1 vcM96CutCaps vcM96CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM97Cut_layer0 : gridLayerCurvatureOK
    vcM97CutCell vcM97CutRoots 1 1 1 vcM97CutCaps vcM97CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM98Cut_layer0 : gridLayerCurvatureOK
    vcM98CutCell vcM98CutRoots 1 1 1 vcM98CutCaps vcM98CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM99Cut_layer0 : gridLayerCurvatureOK
    vcM99CutCell vcM99CutRoots 1 1 1 vcM99CutCaps vcM99CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM100Cut_layer0 : gridLayerCurvatureOK
    vcM100CutCell vcM100CutRoots 1 1 1 vcM100CutCaps vcM100CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
