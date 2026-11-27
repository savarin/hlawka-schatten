/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs128
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs128

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem vcM149Cut_layer0 : gridLayerCurvatureOK
    vcM149CutCell vcM149CutRoots 1 1 1 vcM149CutCaps vcM149CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM150Cut_layer0 : gridLayerCurvatureOK
    vcM150CutCell vcM150CutRoots 1 1 1 vcM150CutCaps vcM150CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM151Cut_layer0 : gridLayerCurvatureOK
    vcM151CutCell vcM151CutRoots 1 1 1 vcM151CutCaps vcM151CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM152Cut_layer0 : gridLayerCurvatureOK
    vcM152CutCell vcM152CutRoots 1 1 1 vcM152CutCaps vcM152CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM153Cut_layer0 : gridLayerCurvatureOK
    vcM153CutCell vcM153CutRoots 1 1 1 vcM153CutCaps vcM153CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM154Cut_layer0 : gridLayerCurvatureOK
    vcM154CutCell vcM154CutRoots 1 1 1 vcM154CutCaps vcM154CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM155Cut_layer0 : gridLayerCurvatureOK
    vcM155CutCell vcM155CutRoots 2 2 1 vcM155CutCaps vcM155CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM155Cut_layer1 : gridLayerCurvatureOK
    vcM155CutCell vcM155CutRoots 2 2 1 vcM155CutCaps vcM155CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM156Cut_layer0 : gridLayerCurvatureOK
    vcM156CutCell vcM156CutRoots 1 1 1 vcM156CutCaps vcM156CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM157Cut_layer0 : gridLayerCurvatureOK
    vcM157CutCell vcM157CutRoots 1 1 1 vcM157CutCaps vcM157CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM158Cut_layer0 : gridLayerCurvatureOK
    vcM158CutCell vcM158CutRoots 1 1 1 vcM158CutCaps vcM158CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM159Cut_layer0 : gridLayerCurvatureOK
    vcM159CutCell vcM159CutRoots 1 1 1 vcM159CutCaps vcM159CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM160Cut_layer0 : gridLayerCurvatureOK
    vcM160CutCell vcM160CutRoots 1 1 1 vcM160CutCaps vcM160CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM161Cut_layer0 : gridLayerCurvatureOK
    vcM161CutCell vcM161CutRoots 1 1 1 vcM161CutCaps vcM161CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM162Cut_layer0 : gridLayerCurvatureOK
    vcM162CutCell vcM162CutRoots 1 1 1 vcM162CutCaps vcM162CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM163Cut_layer0 : gridLayerCurvatureOK
    vcM163CutCell vcM163CutRoots 1 1 1 vcM163CutCaps vcM163CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM164Cut_layer0 : gridLayerCurvatureOK
    vcM164CutCell vcM164CutRoots 1 1 1 vcM164CutCaps vcM164CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM165Cut_layer0 : gridLayerCurvatureOK
    vcM165CutCell vcM165CutRoots 1 1 1 vcM165CutCaps vcM165CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM166Cut_layer0 : gridLayerCurvatureOK
    vcM166CutCell vcM166CutRoots 1 1 1 vcM166CutCaps vcM166CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM167Cut_layer0 : gridLayerCurvatureOK
    vcM167CutCell vcM167CutRoots 1 1 1 vcM167CutCaps vcM167CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM168Cut_layer0 : gridLayerCurvatureOK
    vcM168CutCell vcM168CutRoots 1 1 1 vcM168CutCaps vcM168CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM169Cut_layer0 : gridLayerCurvatureOK
    vcM169CutCell vcM169CutRoots 1 1 1 vcM169CutCaps vcM169CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM170Cut_layer0 : gridLayerCurvatureOK
    vcM170CutCell vcM170CutRoots 1 1 1 vcM170CutCaps vcM170CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM171Cut_layer0 : gridLayerCurvatureOK
    vcM171CutCell vcM171CutRoots 1 1 1 vcM171CutCaps vcM171CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM172Cut_layer0 : gridLayerCurvatureOK
    vcM172CutCell vcM172CutRoots 1 1 1 vcM172CutCaps vcM172CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM173Cut_layer0 : gridLayerCurvatureOK
    vcM173CutCell vcM173CutRoots 1 1 1 vcM173CutCaps vcM173CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM174Cut_layer0 : gridLayerCurvatureOK
    vcM174CutCell vcM174CutRoots 1 1 1 vcM174CutCaps vcM174CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM175Cut_layer0 : gridLayerCurvatureOK
    vcM175CutCell vcM175CutRoots 1 1 1 vcM175CutCaps vcM175CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM176Cut_layer0 : gridLayerCurvatureOK
    vcM176CutCell vcM176CutRoots 1 1 1 vcM176CutCaps vcM176CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM177Cut_layer0 : gridLayerCurvatureOK
    vcM177CutCell vcM177CutRoots 1 1 1 vcM177CutCaps vcM177CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
