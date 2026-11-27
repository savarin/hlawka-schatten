/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs192
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs192

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem scS192Cut_layer0 : gridLayerCurvatureOK
    scS192CutCell scS192CutRoots 1 1 1 scS192CutCaps scS192CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS193Cut_layer0 : gridLayerCurvatureOK
    scS193CutCell scS193CutRoots 1 1 1 scS193CutCaps scS193CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS194Cut_layer0 : gridLayerCurvatureOK
    scS194CutCell scS194CutRoots 1 1 1 scS194CutCaps scS194CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS195Cut_layer0 : gridLayerCurvatureOK
    scS195CutCell scS195CutRoots 1 1 1 scS195CutCaps scS195CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS196Cut_layer0 : gridLayerCurvatureOK
    scS196CutCell scS196CutRoots 1 1 1 scS196CutCaps scS196CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS197Cut_layer0 : gridLayerCurvatureOK
    scS197CutCell scS197CutRoots 1 1 1 scS197CutCaps scS197CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS198Cut_layer0 : gridLayerCurvatureOK
    scS198CutCell scS198CutRoots 1 1 1 scS198CutCaps scS198CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS199Cut_layer0 : gridLayerCurvatureOK
    scS199CutCell scS199CutRoots 1 1 1 scS199CutCaps scS199CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS200Cut_layer0 : gridLayerCurvatureOK
    scS200CutCell scS200CutRoots 1 1 1 scS200CutCaps scS200CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS201Cut_layer0 : gridLayerCurvatureOK
    scS201CutCell scS201CutRoots 1 1 1 scS201CutCaps scS201CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS202Cut_layer0 : gridLayerCurvatureOK
    scS202CutCell scS202CutRoots 1 1 1 scS202CutCaps scS202CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS203Cut_layer0 : gridLayerCurvatureOK
    scS203CutCell scS203CutRoots 1 1 1 scS203CutCaps scS203CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD0Cut_layer0 : gridLayerCurvatureOK
    scD0CutCell scD0CutRoots 1 1 1 scD0CutCaps scD0CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD1Cut_layer0 : gridLayerCurvatureOK
    scD1CutCell scD1CutRoots 1 1 1 scD1CutCaps scD1CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD2Cut_layer0 : gridLayerCurvatureOK
    scD2CutCell scD2CutRoots 1 1 1 scD2CutCaps scD2CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD3Cut_layer0 : gridLayerCurvatureOK
    scD3CutCell scD3CutRoots 1 1 1 scD3CutCaps scD3CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD4Cut_layer0 : gridLayerCurvatureOK
    scD4CutCell scD4CutRoots 1 1 1 scD4CutCaps scD4CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD5Cut_layer0 : gridLayerCurvatureOK
    scD5CutCell scD5CutRoots 1 1 1 scD5CutCaps scD5CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD6Cut_layer0 : gridLayerCurvatureOK
    scD6CutCell scD6CutRoots 1 1 1 scD6CutCaps scD6CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD7Cut_layer0 : gridLayerCurvatureOK
    scD7CutCell scD7CutRoots 1 1 1 scD7CutCaps scD7CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD8Cut_layer0 : gridLayerCurvatureOK
    scD8CutCell scD8CutRoots 1 1 1 scD8CutCaps scD8CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD9Cut_layer0 : gridLayerCurvatureOK
    scD9CutCell scD9CutRoots 1 1 1 scD9CutCaps scD9CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD10Cut_layer0 : gridLayerCurvatureOK
    scD10CutCell scD10CutRoots 1 1 1 scD10CutCaps scD10CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD11Cut_layer0 : gridLayerCurvatureOK
    scD11CutCell scD11CutRoots 1 1 1 scD11CutCaps scD11CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD12Cut_layer0 : gridLayerCurvatureOK
    scD12CutCell scD12CutRoots 1 1 1 scD12CutCaps scD12CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD13Cut_layer0 : gridLayerCurvatureOK
    scD13CutCell scD13CutRoots 1 1 1 scD13CutCaps scD13CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD14Cut_layer0 : gridLayerCurvatureOK
    scD14CutCell scD14CutRoots 1 1 1 scD14CutCaps scD14CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD15Cut_layer0 : gridLayerCurvatureOK
    scD15CutCell scD15CutRoots 1 1 1 scD15CutCaps scD15CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD16Cut_layer0 : gridLayerCurvatureOK
    scD16CutCell scD16CutRoots 1 1 1 scD16CutCaps scD16CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD17Cut_layer0 : gridLayerCurvatureOK
    scD17CutCell scD17CutRoots 1 1 1 scD17CutCaps scD17CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD18Cut_layer0 : gridLayerCurvatureOK
    scD18CutCell scD18CutRoots 1 1 1 scD18CutCaps scD18CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD19Cut_layer0 : gridLayerCurvatureOK
    scD19CutCell scD19CutRoots 1 1 1 scD19CutCaps scD19CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
