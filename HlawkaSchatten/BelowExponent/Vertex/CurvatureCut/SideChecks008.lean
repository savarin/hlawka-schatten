/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs256
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs256

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem scD52Cut_layer0 : gridLayerCurvatureOK
    scD52CutCell scD52CutRoots 1 1 1 scD52CutCaps scD52CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD53Cut_layer0 : gridLayerCurvatureOK
    scD53CutCell scD53CutRoots 1 1 1 scD53CutCaps scD53CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD54Cut_layer0 : gridLayerCurvatureOK
    scD54CutCell scD54CutRoots 1 1 1 scD54CutCaps scD54CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD55Cut_layer0 : gridLayerCurvatureOK
    scD55CutCell scD55CutRoots 1 1 1 scD55CutCaps scD55CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD56Cut_layer0 : gridLayerCurvatureOK
    scD56CutCell scD56CutRoots 1 1 1 scD56CutCaps scD56CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD57Cut_layer0 : gridLayerCurvatureOK
    scD57CutCell scD57CutRoots 1 1 1 scD57CutCaps scD57CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD58Cut_layer0 : gridLayerCurvatureOK
    scD58CutCell scD58CutRoots 1 1 1 scD58CutCaps scD58CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD59Cut_layer0 : gridLayerCurvatureOK
    scD59CutCell scD59CutRoots 1 1 1 scD59CutCaps scD59CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD60Cut_layer0 : gridLayerCurvatureOK
    scD60CutCell scD60CutRoots 1 1 1 scD60CutCaps scD60CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD61Cut_layer0 : gridLayerCurvatureOK
    scD61CutCell scD61CutRoots 1 1 1 scD61CutCaps scD61CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD62Cut_layer0 : gridLayerCurvatureOK
    scD62CutCell scD62CutRoots 1 1 1 scD62CutCaps scD62CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD63Cut_layer0 : gridLayerCurvatureOK
    scD63CutCell scD63CutRoots 1 1 1 scD63CutCaps scD63CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD64Cut_layer0 : gridLayerCurvatureOK
    scD64CutCell scD64CutRoots 1 1 1 scD64CutCaps scD64CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD65Cut_layer0 : gridLayerCurvatureOK
    scD65CutCell scD65CutRoots 1 1 1 scD65CutCaps scD65CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD66Cut_layer0 : gridLayerCurvatureOK
    scD66CutCell scD66CutRoots 1 1 1 scD66CutCaps scD66CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD67Cut_layer0 : gridLayerCurvatureOK
    scD67CutCell scD67CutRoots 1 1 1 scD67CutCaps scD67CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD68Cut_layer0 : gridLayerCurvatureOK
    scD68CutCell scD68CutRoots 1 1 1 scD68CutCaps scD68CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD69Cut_layer0 : gridLayerCurvatureOK
    scD69CutCell scD69CutRoots 1 1 1 scD69CutCaps scD69CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD70Cut_layer0 : gridLayerCurvatureOK
    scD70CutCell scD70CutRoots 1 1 1 scD70CutCaps scD70CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD71Cut_layer0 : gridLayerCurvatureOK
    scD71CutCell scD71CutRoots 1 1 1 scD71CutCaps scD71CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD72Cut_layer0 : gridLayerCurvatureOK
    scD72CutCell scD72CutRoots 1 1 1 scD72CutCaps scD72CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD73Cut_layer0 : gridLayerCurvatureOK
    scD73CutCell scD73CutRoots 1 1 1 scD73CutCaps scD73CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD74Cut_layer0 : gridLayerCurvatureOK
    scD74CutCell scD74CutRoots 1 1 1 scD74CutCaps scD74CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD75Cut_layer0 : gridLayerCurvatureOK
    scD75CutCell scD75CutRoots 1 1 1 scD75CutCaps scD75CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD76Cut_layer0 : gridLayerCurvatureOK
    scD76CutCell scD76CutRoots 1 1 1 scD76CutCaps scD76CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD77Cut_layer0 : gridLayerCurvatureOK
    scD77CutCell scD77CutRoots 1 1 1 scD77CutCaps scD77CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD78Cut_layer0 : gridLayerCurvatureOK
    scD78CutCell scD78CutRoots 1 1 1 scD78CutCaps scD78CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD79Cut_layer0 : gridLayerCurvatureOK
    scD79CutCell scD79CutRoots 1 1 1 scD79CutCaps scD79CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD80Cut_layer0 : gridLayerCurvatureOK
    scD80CutCell scD80CutRoots 1 1 1 scD80CutCaps scD80CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD81Cut_layer0 : gridLayerCurvatureOK
    scD81CutCell scD81CutRoots 1 1 1 scD81CutCaps scD81CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD82Cut_layer0 : gridLayerCurvatureOK
    scD82CutCell scD82CutRoots 1 1 1 scD82CutCaps scD82CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD83Cut_layer0 : gridLayerCurvatureOK
    scD83CutCell scD83CutRoots 1 1 1 scD83CutCaps scD83CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
