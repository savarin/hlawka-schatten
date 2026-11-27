/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs128
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs128

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem scS128Cut_layer0 : gridLayerCurvatureOK
    scS128CutCell scS128CutRoots 1 1 1 scS128CutCaps scS128CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS129Cut_layer0 : gridLayerCurvatureOK
    scS129CutCell scS129CutRoots 1 1 1 scS129CutCaps scS129CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS130Cut_layer0 : gridLayerCurvatureOK
    scS130CutCell scS130CutRoots 1 1 1 scS130CutCaps scS130CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS131Cut_layer0 : gridLayerCurvatureOK
    scS131CutCell scS131CutRoots 1 1 1 scS131CutCaps scS131CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS132Cut_layer0 : gridLayerCurvatureOK
    scS132CutCell scS132CutRoots 1 1 1 scS132CutCaps scS132CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS133Cut_layer0 : gridLayerCurvatureOK
    scS133CutCell scS133CutRoots 1 1 1 scS133CutCaps scS133CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS134Cut_layer0 : gridLayerCurvatureOK
    scS134CutCell scS134CutRoots 1 1 1 scS134CutCaps scS134CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS135Cut_layer0 : gridLayerCurvatureOK
    scS135CutCell scS135CutRoots 1 1 1 scS135CutCaps scS135CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS136Cut_layer0 : gridLayerCurvatureOK
    scS136CutCell scS136CutRoots 1 1 1 scS136CutCaps scS136CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS137Cut_layer0 : gridLayerCurvatureOK
    scS137CutCell scS137CutRoots 1 1 1 scS137CutCaps scS137CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS138Cut_layer0 : gridLayerCurvatureOK
    scS138CutCell scS138CutRoots 1 1 1 scS138CutCaps scS138CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS139Cut_layer0 : gridLayerCurvatureOK
    scS139CutCell scS139CutRoots 1 1 1 scS139CutCaps scS139CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS140Cut_layer0 : gridLayerCurvatureOK
    scS140CutCell scS140CutRoots 1 1 1 scS140CutCaps scS140CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS141Cut_layer0 : gridLayerCurvatureOK
    scS141CutCell scS141CutRoots 1 1 1 scS141CutCaps scS141CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS142Cut_layer0 : gridLayerCurvatureOK
    scS142CutCell scS142CutRoots 1 1 1 scS142CutCaps scS142CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS143Cut_layer0 : gridLayerCurvatureOK
    scS143CutCell scS143CutRoots 1 1 1 scS143CutCaps scS143CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS144Cut_layer0 : gridLayerCurvatureOK
    scS144CutCell scS144CutRoots 1 1 1 scS144CutCaps scS144CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS145Cut_layer0 : gridLayerCurvatureOK
    scS145CutCell scS145CutRoots 1 1 1 scS145CutCaps scS145CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS146Cut_layer0 : gridLayerCurvatureOK
    scS146CutCell scS146CutRoots 1 1 1 scS146CutCaps scS146CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS147Cut_layer0 : gridLayerCurvatureOK
    scS147CutCell scS147CutRoots 1 1 1 scS147CutCaps scS147CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS148Cut_layer0 : gridLayerCurvatureOK
    scS148CutCell scS148CutRoots 1 1 1 scS148CutCaps scS148CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS149Cut_layer0 : gridLayerCurvatureOK
    scS149CutCell scS149CutRoots 1 1 1 scS149CutCaps scS149CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS150Cut_layer0 : gridLayerCurvatureOK
    scS150CutCell scS150CutRoots 1 1 1 scS150CutCaps scS150CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS151Cut_layer0 : gridLayerCurvatureOK
    scS151CutCell scS151CutRoots 1 1 1 scS151CutCaps scS151CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS152Cut_layer0 : gridLayerCurvatureOK
    scS152CutCell scS152CutRoots 1 1 1 scS152CutCaps scS152CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS153Cut_layer0 : gridLayerCurvatureOK
    scS153CutCell scS153CutRoots 1 1 1 scS153CutCaps scS153CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS154Cut_layer0 : gridLayerCurvatureOK
    scS154CutCell scS154CutRoots 1 1 1 scS154CutCaps scS154CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS155Cut_layer0 : gridLayerCurvatureOK
    scS155CutCell scS155CutRoots 1 1 1 scS155CutCaps scS155CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS156Cut_layer0 : gridLayerCurvatureOK
    scS156CutCell scS156CutRoots 1 1 1 scS156CutCaps scS156CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS157Cut_layer0 : gridLayerCurvatureOK
    scS157CutCell scS157CutRoots 1 1 1 scS157CutCaps scS157CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS158Cut_layer0 : gridLayerCurvatureOK
    scS158CutCell scS158CutRoots 1 1 1 scS158CutCaps scS158CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS159Cut_layer0 : gridLayerCurvatureOK
    scS159CutCell scS159CutRoots 1 1 1 scS159CutCaps scS159CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
