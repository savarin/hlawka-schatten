/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs288
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs288

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem scD84Cut_layer0 : gridLayerCurvatureOK
    scD84CutCell scD84CutRoots 1 1 1 scD84CutCaps scD84CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD85Cut_layer0 : gridLayerCurvatureOK
    scD85CutCell scD85CutRoots 1 1 1 scD85CutCaps scD85CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD86Cut_layer0 : gridLayerCurvatureOK
    scD86CutCell scD86CutRoots 1 1 1 scD86CutCaps scD86CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD87Cut_layer0 : gridLayerCurvatureOK
    scD87CutCell scD87CutRoots 1 1 1 scD87CutCaps scD87CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD88Cut_layer0 : gridLayerCurvatureOK
    scD88CutCell scD88CutRoots 1 1 1 scD88CutCaps scD88CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD89Cut_layer0 : gridLayerCurvatureOK
    scD89CutCell scD89CutRoots 1 1 1 scD89CutCaps scD89CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD90Cut_layer0 : gridLayerCurvatureOK
    scD90CutCell scD90CutRoots 1 1 1 scD90CutCaps scD90CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD91Cut_layer0 : gridLayerCurvatureOK
    scD91CutCell scD91CutRoots 1 1 1 scD91CutCaps scD91CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD92Cut_layer0 : gridLayerCurvatureOK
    scD92CutCell scD92CutRoots 1 1 1 scD92CutCaps scD92CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD93Cut_layer0 : gridLayerCurvatureOK
    scD93CutCell scD93CutRoots 1 1 1 scD93CutCaps scD93CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD94Cut_layer0 : gridLayerCurvatureOK
    scD94CutCell scD94CutRoots 1 1 1 scD94CutCaps scD94CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD95Cut_layer0 : gridLayerCurvatureOK
    scD95CutCell scD95CutRoots 1 1 1 scD95CutCaps scD95CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD96Cut_layer0 : gridLayerCurvatureOK
    scD96CutCell scD96CutRoots 1 1 1 scD96CutCaps scD96CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD97Cut_layer0 : gridLayerCurvatureOK
    scD97CutCell scD97CutRoots 1 1 1 scD97CutCaps scD97CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD98Cut_layer0 : gridLayerCurvatureOK
    scD98CutCell scD98CutRoots 1 1 1 scD98CutCaps scD98CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD99Cut_layer0 : gridLayerCurvatureOK
    scD99CutCell scD99CutRoots 1 1 1 scD99CutCaps scD99CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD100Cut_layer0 : gridLayerCurvatureOK
    scD100CutCell scD100CutRoots 1 1 1 scD100CutCaps scD100CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD101Cut_layer0 : gridLayerCurvatureOK
    scD101CutCell scD101CutRoots 1 1 1 scD101CutCaps scD101CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE0Cut_layer0 : gridLayerCurvatureOK
    scE0CutCell scE0CutRoots 1 1 1 scE0CutCaps scE0CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE1Cut_layer0 : gridLayerCurvatureOK
    scE1CutCell scE1CutRoots 1 1 1 scE1CutCaps scE1CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE2Cut_layer0 : gridLayerCurvatureOK
    scE2CutCell scE2CutRoots 1 1 1 scE2CutCaps scE2CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE3Cut_layer0 : gridLayerCurvatureOK
    scE3CutCell scE3CutRoots 1 1 1 scE3CutCaps scE3CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE4Cut_layer0 : gridLayerCurvatureOK
    scE4CutCell scE4CutRoots 1 1 1 scE4CutCaps scE4CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE5Cut_layer0 : gridLayerCurvatureOK
    scE5CutCell scE5CutRoots 1 1 1 scE5CutCaps scE5CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE6Cut_layer0 : gridLayerCurvatureOK
    scE6CutCell scE6CutRoots 1 1 1 scE6CutCaps scE6CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE7Cut_layer0 : gridLayerCurvatureOK
    scE7CutCell scE7CutRoots 1 1 1 scE7CutCaps scE7CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE8Cut_layer0 : gridLayerCurvatureOK
    scE8CutCell scE8CutRoots 1 1 1 scE8CutCaps scE8CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE9Cut_layer0 : gridLayerCurvatureOK
    scE9CutCell scE9CutRoots 1 1 1 scE9CutCaps scE9CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE10Cut_layer0 : gridLayerCurvatureOK
    scE10CutCell scE10CutRoots 1 1 1 scE10CutCaps scE10CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE11Cut_layer0 : gridLayerCurvatureOK
    scE11CutCell scE11CutRoots 1 1 1 scE11CutCaps scE11CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE12Cut_layer0 : gridLayerCurvatureOK
    scE12CutCell scE12CutRoots 1 1 1 scE12CutCaps scE12CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE13Cut_layer0 : gridLayerCurvatureOK
    scE13CutCell scE13CutRoots 1 1 1 scE13CutCaps scE13CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
