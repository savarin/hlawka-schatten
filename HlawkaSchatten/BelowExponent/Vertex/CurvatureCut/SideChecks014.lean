/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs448
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs448

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem scE142Cut_layer0 : gridLayerCurvatureOK
    scE142CutCell scE142CutRoots 1 1 1 scE142CutCaps scE142CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE143Cut_layer0 : gridLayerCurvatureOK
    scE143CutCell scE143CutRoots 1 1 1 scE143CutCaps scE143CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE144Cut_layer0 : gridLayerCurvatureOK
    scE144CutCell scE144CutRoots 1 1 1 scE144CutCaps scE144CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE145Cut_layer0 : gridLayerCurvatureOK
    scE145CutCell scE145CutRoots 1 1 1 scE145CutCaps scE145CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE146Cut_layer0 : gridLayerCurvatureOK
    scE146CutCell scE146CutRoots 1 1 1 scE146CutCaps scE146CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE147Cut_layer0 : gridLayerCurvatureOK
    scE147CutCell scE147CutRoots 1 1 1 scE147CutCaps scE147CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE148Cut_layer0 : gridLayerCurvatureOK
    scE148CutCell scE148CutRoots 1 1 1 scE148CutCaps scE148CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE149Cut_layer0 : gridLayerCurvatureOK
    scE149CutCell scE149CutRoots 1 1 1 scE149CutCaps scE149CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE150Cut_layer0 : gridLayerCurvatureOK
    scE150CutCell scE150CutRoots 1 1 1 scE150CutCaps scE150CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE151Cut_layer0 : gridLayerCurvatureOK
    scE151CutCell scE151CutRoots 1 1 1 scE151CutCaps scE151CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE152Cut_layer0 : gridLayerCurvatureOK
    scE152CutCell scE152CutRoots 1 1 1 scE152CutCaps scE152CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE153Cut_layer0 : gridLayerCurvatureOK
    scE153CutCell scE153CutRoots 1 1 1 scE153CutCaps scE153CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE154Cut_layer0 : gridLayerCurvatureOK
    scE154CutCell scE154CutRoots 1 1 1 scE154CutCaps scE154CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE155Cut_layer0 : gridLayerCurvatureOK
    scE155CutCell scE155CutRoots 1 1 1 scE155CutCaps scE155CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE156Cut_layer0 : gridLayerCurvatureOK
    scE156CutCell scE156CutRoots 1 1 1 scE156CutCaps scE156CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE157Cut_layer0 : gridLayerCurvatureOK
    scE157CutCell scE157CutRoots 1 1 1 scE157CutCaps scE157CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE158Cut_layer0 : gridLayerCurvatureOK
    scE158CutCell scE158CutRoots 1 1 1 scE158CutCaps scE158CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE159Cut_layer0 : gridLayerCurvatureOK
    scE159CutCell scE159CutRoots 1 1 1 scE159CutCaps scE159CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE160Cut_layer0 : gridLayerCurvatureOK
    scE160CutCell scE160CutRoots 1 1 1 scE160CutCaps scE160CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE161Cut_layer0 : gridLayerCurvatureOK
    scE161CutCell scE161CutRoots 1 1 1 scE161CutCaps scE161CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE162Cut_layer0 : gridLayerCurvatureOK
    scE162CutCell scE162CutRoots 1 1 1 scE162CutCaps scE162CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE163Cut_layer0 : gridLayerCurvatureOK
    scE163CutCell scE163CutRoots 1 1 1 scE163CutCaps scE163CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE164Cut_layer0 : gridLayerCurvatureOK
    scE164CutCell scE164CutRoots 1 1 1 scE164CutCaps scE164CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE165Cut_layer0 : gridLayerCurvatureOK
    scE165CutCell scE165CutRoots 1 1 1 scE165CutCaps scE165CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE166Cut_layer0 : gridLayerCurvatureOK
    scE166CutCell scE166CutRoots 1 1 1 scE166CutCaps scE166CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE167Cut_layer0 : gridLayerCurvatureOK
    scE167CutCell scE167CutRoots 1 1 1 scE167CutCaps scE167CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE168Cut_layer0 : gridLayerCurvatureOK
    scE168CutCell scE168CutRoots 1 1 1 scE168CutCaps scE168CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE169Cut_layer0 : gridLayerCurvatureOK
    scE169CutCell scE169CutRoots 1 1 1 scE169CutCaps scE169CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE170Cut_layer0 : gridLayerCurvatureOK
    scE170CutCell scE170CutRoots 1 1 1 scE170CutCaps scE170CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE171Cut_layer0 : gridLayerCurvatureOK
    scE171CutCell scE171CutRoots 1 1 1 scE171CutCaps scE171CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE172Cut_layer0 : gridLayerCurvatureOK
    scE172CutCell scE172CutRoots 1 1 1 scE172CutCaps scE172CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE173Cut_layer0 : gridLayerCurvatureOK
    scE173CutCell scE173CutRoots 1 1 1 scE173CutCaps scE173CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
