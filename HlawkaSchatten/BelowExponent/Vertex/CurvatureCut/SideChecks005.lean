/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs160
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs160

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem scS160Cut_layer0 : gridLayerCurvatureOK
    scS160CutCell scS160CutRoots 1 1 1 scS160CutCaps scS160CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS161Cut_layer0 : gridLayerCurvatureOK
    scS161CutCell scS161CutRoots 1 1 1 scS161CutCaps scS161CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS162Cut_layer0 : gridLayerCurvatureOK
    scS162CutCell scS162CutRoots 1 1 1 scS162CutCaps scS162CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS163Cut_layer0 : gridLayerCurvatureOK
    scS163CutCell scS163CutRoots 1 1 1 scS163CutCaps scS163CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS164Cut_layer0 : gridLayerCurvatureOK
    scS164CutCell scS164CutRoots 1 1 1 scS164CutCaps scS164CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS165Cut_layer0 : gridLayerCurvatureOK
    scS165CutCell scS165CutRoots 1 1 1 scS165CutCaps scS165CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS166Cut_layer0 : gridLayerCurvatureOK
    scS166CutCell scS166CutRoots 1 1 1 scS166CutCaps scS166CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS167Cut_layer0 : gridLayerCurvatureOK
    scS167CutCell scS167CutRoots 1 1 1 scS167CutCaps scS167CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS168Cut_layer0 : gridLayerCurvatureOK
    scS168CutCell scS168CutRoots 1 1 1 scS168CutCaps scS168CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS169Cut_layer0 : gridLayerCurvatureOK
    scS169CutCell scS169CutRoots 1 1 1 scS169CutCaps scS169CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS170Cut_layer0 : gridLayerCurvatureOK
    scS170CutCell scS170CutRoots 1 1 1 scS170CutCaps scS170CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS171Cut_layer0 : gridLayerCurvatureOK
    scS171CutCell scS171CutRoots 1 1 1 scS171CutCaps scS171CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS172Cut_layer0 : gridLayerCurvatureOK
    scS172CutCell scS172CutRoots 1 1 1 scS172CutCaps scS172CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS173Cut_layer0 : gridLayerCurvatureOK
    scS173CutCell scS173CutRoots 1 1 1 scS173CutCaps scS173CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS174Cut_layer0 : gridLayerCurvatureOK
    scS174CutCell scS174CutRoots 1 1 1 scS174CutCaps scS174CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS175Cut_layer0 : gridLayerCurvatureOK
    scS175CutCell scS175CutRoots 1 1 1 scS175CutCaps scS175CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS176Cut_layer0 : gridLayerCurvatureOK
    scS176CutCell scS176CutRoots 1 1 1 scS176CutCaps scS176CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS177Cut_layer0 : gridLayerCurvatureOK
    scS177CutCell scS177CutRoots 1 1 1 scS177CutCaps scS177CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS178Cut_layer0 : gridLayerCurvatureOK
    scS178CutCell scS178CutRoots 1 1 1 scS178CutCaps scS178CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS179Cut_layer0 : gridLayerCurvatureOK
    scS179CutCell scS179CutRoots 1 1 1 scS179CutCaps scS179CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS180Cut_layer0 : gridLayerCurvatureOK
    scS180CutCell scS180CutRoots 1 1 1 scS180CutCaps scS180CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS181Cut_layer0 : gridLayerCurvatureOK
    scS181CutCell scS181CutRoots 1 1 1 scS181CutCaps scS181CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS182Cut_layer0 : gridLayerCurvatureOK
    scS182CutCell scS182CutRoots 1 1 1 scS182CutCaps scS182CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS183Cut_layer0 : gridLayerCurvatureOK
    scS183CutCell scS183CutRoots 1 1 1 scS183CutCaps scS183CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS184Cut_layer0 : gridLayerCurvatureOK
    scS184CutCell scS184CutRoots 1 1 1 scS184CutCaps scS184CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS185Cut_layer0 : gridLayerCurvatureOK
    scS185CutCell scS185CutRoots 1 1 1 scS185CutCaps scS185CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS186Cut_layer0 : gridLayerCurvatureOK
    scS186CutCell scS186CutRoots 1 1 1 scS186CutCaps scS186CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS187Cut_layer0 : gridLayerCurvatureOK
    scS187CutCell scS187CutRoots 1 1 1 scS187CutCaps scS187CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS188Cut_layer0 : gridLayerCurvatureOK
    scS188CutCell scS188CutRoots 1 1 1 scS188CutCaps scS188CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS189Cut_layer0 : gridLayerCurvatureOK
    scS189CutCell scS189CutRoots 1 1 1 scS189CutCaps scS189CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS190Cut_layer0 : gridLayerCurvatureOK
    scS190CutCell scS190CutRoots 1 1 1 scS190CutCaps scS190CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS191Cut_layer0 : gridLayerCurvatureOK
    scS191CutCell scS191CutRoots 1 1 1 scS191CutCaps scS191CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
