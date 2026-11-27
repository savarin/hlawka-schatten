/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs000
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs000

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem scS0Cut_layer0 : gridLayerCurvatureOK
    scS0CutCell scS0CutRoots 1 1 1 scS0CutCaps scS0CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS1Cut_layer0 : gridLayerCurvatureOK
    scS1CutCell scS1CutRoots 1 1 1 scS1CutCaps scS1CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS2Cut_layer0 : gridLayerCurvatureOK
    scS2CutCell scS2CutRoots 1 1 1 scS2CutCaps scS2CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS3Cut_layer0 : gridLayerCurvatureOK
    scS3CutCell scS3CutRoots 1 1 1 scS3CutCaps scS3CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS4Cut_layer0 : gridLayerCurvatureOK
    scS4CutCell scS4CutRoots 1 1 1 scS4CutCaps scS4CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS5Cut_layer0 : gridLayerCurvatureOK
    scS5CutCell scS5CutRoots 1 1 1 scS5CutCaps scS5CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS6Cut_layer0 : gridLayerCurvatureOK
    scS6CutCell scS6CutRoots 1 1 1 scS6CutCaps scS6CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS7Cut_layer0 : gridLayerCurvatureOK
    scS7CutCell scS7CutRoots 1 1 1 scS7CutCaps scS7CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS8Cut_layer0 : gridLayerCurvatureOK
    scS8CutCell scS8CutRoots 1 1 1 scS8CutCaps scS8CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS9Cut_layer0 : gridLayerCurvatureOK
    scS9CutCell scS9CutRoots 1 1 1 scS9CutCaps scS9CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS10Cut_layer0 : gridLayerCurvatureOK
    scS10CutCell scS10CutRoots 1 1 1 scS10CutCaps scS10CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS11Cut_layer0 : gridLayerCurvatureOK
    scS11CutCell scS11CutRoots 1 1 1 scS11CutCaps scS11CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS12Cut_layer0 : gridLayerCurvatureOK
    scS12CutCell scS12CutRoots 1 1 1 scS12CutCaps scS12CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS13Cut_layer0 : gridLayerCurvatureOK
    scS13CutCell scS13CutRoots 1 1 1 scS13CutCaps scS13CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS14Cut_layer0 : gridLayerCurvatureOK
    scS14CutCell scS14CutRoots 1 1 1 scS14CutCaps scS14CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS15Cut_layer0 : gridLayerCurvatureOK
    scS15CutCell scS15CutRoots 1 1 1 scS15CutCaps scS15CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS16Cut_layer0 : gridLayerCurvatureOK
    scS16CutCell scS16CutRoots 1 1 1 scS16CutCaps scS16CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS17Cut_layer0 : gridLayerCurvatureOK
    scS17CutCell scS17CutRoots 1 1 1 scS17CutCaps scS17CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS18Cut_layer0 : gridLayerCurvatureOK
    scS18CutCell scS18CutRoots 1 1 1 scS18CutCaps scS18CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS19Cut_layer0 : gridLayerCurvatureOK
    scS19CutCell scS19CutRoots 1 1 1 scS19CutCaps scS19CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS20Cut_layer0 : gridLayerCurvatureOK
    scS20CutCell scS20CutRoots 1 1 1 scS20CutCaps scS20CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS21Cut_layer0 : gridLayerCurvatureOK
    scS21CutCell scS21CutRoots 1 1 1 scS21CutCaps scS21CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS22Cut_layer0 : gridLayerCurvatureOK
    scS22CutCell scS22CutRoots 1 1 1 scS22CutCaps scS22CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS23Cut_layer0 : gridLayerCurvatureOK
    scS23CutCell scS23CutRoots 1 1 1 scS23CutCaps scS23CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS24Cut_layer0 : gridLayerCurvatureOK
    scS24CutCell scS24CutRoots 1 1 1 scS24CutCaps scS24CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS25Cut_layer0 : gridLayerCurvatureOK
    scS25CutCell scS25CutRoots 1 1 1 scS25CutCaps scS25CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS26Cut_layer0 : gridLayerCurvatureOK
    scS26CutCell scS26CutRoots 1 1 1 scS26CutCaps scS26CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS27Cut_layer0 : gridLayerCurvatureOK
    scS27CutCell scS27CutRoots 1 1 1 scS27CutCaps scS27CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS28Cut_layer0 : gridLayerCurvatureOK
    scS28CutCell scS28CutRoots 1 1 1 scS28CutCaps scS28CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS29Cut_layer0 : gridLayerCurvatureOK
    scS29CutCell scS29CutRoots 1 1 1 scS29CutCaps scS29CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS30Cut_layer0 : gridLayerCurvatureOK
    scS30CutCell scS30CutRoots 1 1 1 scS30CutCaps scS30CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS31Cut_layer0 : gridLayerCurvatureOK
    scS31CutCell scS31CutRoots 1 1 1 scS31CutCaps scS31CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
