/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs096
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs128
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs096
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs128

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem vcM126Cut_layer0 : gridLayerCurvatureOK
    vcM126CutCell vcM126CutRoots 1 1 1 vcM126CutCaps vcM126CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM127Cut_layer0 : gridLayerCurvatureOK
    vcM127CutCell vcM127CutRoots 1 1 1 vcM127CutCaps vcM127CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM128Cut_layer0 : gridLayerCurvatureOK
    vcM128CutCell vcM128CutRoots 1 1 1 vcM128CutCaps vcM128CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM129Cut_layer0 : gridLayerCurvatureOK
    vcM129CutCell vcM129CutRoots 1 1 1 vcM129CutCaps vcM129CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM130Cut_layer0 : gridLayerCurvatureOK
    vcM130CutCell vcM130CutRoots 1 1 1 vcM130CutCaps vcM130CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM131Cut_layer0 : gridLayerCurvatureOK
    vcM131CutCell vcM131CutRoots 1 1 1 vcM131CutCaps vcM131CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM132Cut_layer0 : gridLayerCurvatureOK
    vcM132CutCell vcM132CutRoots 1 1 1 vcM132CutCaps vcM132CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM133Cut_layer0 : gridLayerCurvatureOK
    vcM133CutCell vcM133CutRoots 1 1 1 vcM133CutCaps vcM133CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM134Cut_layer0 : gridLayerCurvatureOK
    vcM134CutCell vcM134CutRoots 2 2 1 vcM134CutCaps vcM134CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM134Cut_layer1 : gridLayerCurvatureOK
    vcM134CutCell vcM134CutRoots 2 2 1 vcM134CutCaps vcM134CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM135Cut_layer0 : gridLayerCurvatureOK
    vcM135CutCell vcM135CutRoots 2 2 1 vcM135CutCaps vcM135CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM135Cut_layer1 : gridLayerCurvatureOK
    vcM135CutCell vcM135CutRoots 2 2 1 vcM135CutCaps vcM135CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM136Cut_layer0 : gridLayerCurvatureOK
    vcM136CutCell vcM136CutRoots 1 1 1 vcM136CutCaps vcM136CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM137Cut_layer0 : gridLayerCurvatureOK
    vcM137CutCell vcM137CutRoots 2 2 1 vcM137CutCaps vcM137CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM137Cut_layer1 : gridLayerCurvatureOK
    vcM137CutCell vcM137CutRoots 2 2 1 vcM137CutCaps vcM137CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM138Cut_layer0 : gridLayerCurvatureOK
    vcM138CutCell vcM138CutRoots 1 1 1 vcM138CutCaps vcM138CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM139Cut_layer0 : gridLayerCurvatureOK
    vcM139CutCell vcM139CutRoots 1 1 1 vcM139CutCaps vcM139CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM140Cut_layer0 : gridLayerCurvatureOK
    vcM140CutCell vcM140CutRoots 1 1 1 vcM140CutCaps vcM140CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM141Cut_layer0 : gridLayerCurvatureOK
    vcM141CutCell vcM141CutRoots 1 1 1 vcM141CutCaps vcM141CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM142Cut_layer0 : gridLayerCurvatureOK
    vcM142CutCell vcM142CutRoots 1 1 1 vcM142CutCaps vcM142CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM143Cut_layer0 : gridLayerCurvatureOK
    vcM143CutCell vcM143CutRoots 1 1 1 vcM143CutCaps vcM143CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM144Cut_layer0 : gridLayerCurvatureOK
    vcM144CutCell vcM144CutRoots 1 1 1 vcM144CutCaps vcM144CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM145Cut_layer0 : gridLayerCurvatureOK
    vcM145CutCell vcM145CutRoots 1 1 1 vcM145CutCaps vcM145CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM146Cut_layer0 : gridLayerCurvatureOK
    vcM146CutCell vcM146CutRoots 1 1 1 vcM146CutCaps vcM146CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM147Cut_layer0 : gridLayerCurvatureOK
    vcM147CutCell vcM147CutRoots 1 1 1 vcM147CutCaps vcM147CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM148Cut_layer0 : gridLayerCurvatureOK
    vcM148CutCell vcM148CutRoots 1 1 1 vcM148CutCaps vcM148CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
