/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs032
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs032

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem scS32Cut_layer0 : gridLayerCurvatureOK
    scS32CutCell scS32CutRoots 1 1 1 scS32CutCaps scS32CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS33Cut_layer0 : gridLayerCurvatureOK
    scS33CutCell scS33CutRoots 1 1 1 scS33CutCaps scS33CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS34Cut_layer0 : gridLayerCurvatureOK
    scS34CutCell scS34CutRoots 1 1 1 scS34CutCaps scS34CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS35Cut_layer0 : gridLayerCurvatureOK
    scS35CutCell scS35CutRoots 1 1 1 scS35CutCaps scS35CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS36Cut_layer0 : gridLayerCurvatureOK
    scS36CutCell scS36CutRoots 1 1 1 scS36CutCaps scS36CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS37Cut_layer0 : gridLayerCurvatureOK
    scS37CutCell scS37CutRoots 1 1 1 scS37CutCaps scS37CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS38Cut_layer0 : gridLayerCurvatureOK
    scS38CutCell scS38CutRoots 1 1 1 scS38CutCaps scS38CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS39Cut_layer0 : gridLayerCurvatureOK
    scS39CutCell scS39CutRoots 1 1 1 scS39CutCaps scS39CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS40Cut_layer0 : gridLayerCurvatureOK
    scS40CutCell scS40CutRoots 1 1 1 scS40CutCaps scS40CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS41Cut_layer0 : gridLayerCurvatureOK
    scS41CutCell scS41CutRoots 1 1 1 scS41CutCaps scS41CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS42Cut_layer0 : gridLayerCurvatureOK
    scS42CutCell scS42CutRoots 1 1 1 scS42CutCaps scS42CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS43Cut_layer0 : gridLayerCurvatureOK
    scS43CutCell scS43CutRoots 1 1 1 scS43CutCaps scS43CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS44Cut_layer0 : gridLayerCurvatureOK
    scS44CutCell scS44CutRoots 1 1 1 scS44CutCaps scS44CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS45Cut_layer0 : gridLayerCurvatureOK
    scS45CutCell scS45CutRoots 1 1 1 scS45CutCaps scS45CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS46Cut_layer0 : gridLayerCurvatureOK
    scS46CutCell scS46CutRoots 1 1 1 scS46CutCaps scS46CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS47Cut_layer0 : gridLayerCurvatureOK
    scS47CutCell scS47CutRoots 1 1 1 scS47CutCaps scS47CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS48Cut_layer0 : gridLayerCurvatureOK
    scS48CutCell scS48CutRoots 1 1 1 scS48CutCaps scS48CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS49Cut_layer0 : gridLayerCurvatureOK
    scS49CutCell scS49CutRoots 1 1 1 scS49CutCaps scS49CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS50Cut_layer0 : gridLayerCurvatureOK
    scS50CutCell scS50CutRoots 1 1 1 scS50CutCaps scS50CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS51Cut_layer0 : gridLayerCurvatureOK
    scS51CutCell scS51CutRoots 1 1 1 scS51CutCaps scS51CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS52Cut_layer0 : gridLayerCurvatureOK
    scS52CutCell scS52CutRoots 1 1 1 scS52CutCaps scS52CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS53Cut_layer0 : gridLayerCurvatureOK
    scS53CutCell scS53CutRoots 1 1 1 scS53CutCaps scS53CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS54Cut_layer0 : gridLayerCurvatureOK
    scS54CutCell scS54CutRoots 1 1 1 scS54CutCaps scS54CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS55Cut_layer0 : gridLayerCurvatureOK
    scS55CutCell scS55CutRoots 1 1 1 scS55CutCaps scS55CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS56Cut_layer0 : gridLayerCurvatureOK
    scS56CutCell scS56CutRoots 1 1 1 scS56CutCaps scS56CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS57Cut_layer0 : gridLayerCurvatureOK
    scS57CutCell scS57CutRoots 1 1 1 scS57CutCaps scS57CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS58Cut_layer0 : gridLayerCurvatureOK
    scS58CutCell scS58CutRoots 1 1 1 scS58CutCaps scS58CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS59Cut_layer0 : gridLayerCurvatureOK
    scS59CutCell scS59CutRoots 1 1 1 scS59CutCaps scS59CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS60Cut_layer0 : gridLayerCurvatureOK
    scS60CutCell scS60CutRoots 1 1 1 scS60CutCaps scS60CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS61Cut_layer0 : gridLayerCurvatureOK
    scS61CutCell scS61CutRoots 1 1 1 scS61CutCaps scS61CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS62Cut_layer0 : gridLayerCurvatureOK
    scS62CutCell scS62CutRoots 1 1 1 scS62CutCaps scS62CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scS63Cut_layer0 : gridLayerCurvatureOK
    scS63CutCell scS63CutRoots 1 1 1 scS63CutCaps scS63CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
