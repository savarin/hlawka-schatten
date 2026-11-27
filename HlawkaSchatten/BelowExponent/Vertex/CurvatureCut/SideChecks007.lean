/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs224
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs224

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem scD20Cut_layer0 : gridLayerCurvatureOK
    scD20CutCell scD20CutRoots 1 1 1 scD20CutCaps scD20CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD21Cut_layer0 : gridLayerCurvatureOK
    scD21CutCell scD21CutRoots 1 1 1 scD21CutCaps scD21CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD22Cut_layer0 : gridLayerCurvatureOK
    scD22CutCell scD22CutRoots 1 1 1 scD22CutCaps scD22CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD23Cut_layer0 : gridLayerCurvatureOK
    scD23CutCell scD23CutRoots 1 1 1 scD23CutCaps scD23CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD24Cut_layer0 : gridLayerCurvatureOK
    scD24CutCell scD24CutRoots 1 1 1 scD24CutCaps scD24CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD25Cut_layer0 : gridLayerCurvatureOK
    scD25CutCell scD25CutRoots 1 1 1 scD25CutCaps scD25CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD26Cut_layer0 : gridLayerCurvatureOK
    scD26CutCell scD26CutRoots 1 1 1 scD26CutCaps scD26CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD27Cut_layer0 : gridLayerCurvatureOK
    scD27CutCell scD27CutRoots 1 1 1 scD27CutCaps scD27CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD28Cut_layer0 : gridLayerCurvatureOK
    scD28CutCell scD28CutRoots 1 1 1 scD28CutCaps scD28CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD29Cut_layer0 : gridLayerCurvatureOK
    scD29CutCell scD29CutRoots 1 1 1 scD29CutCaps scD29CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD30Cut_layer0 : gridLayerCurvatureOK
    scD30CutCell scD30CutRoots 1 1 1 scD30CutCaps scD30CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD31Cut_layer0 : gridLayerCurvatureOK
    scD31CutCell scD31CutRoots 1 1 1 scD31CutCaps scD31CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD32Cut_layer0 : gridLayerCurvatureOK
    scD32CutCell scD32CutRoots 1 1 1 scD32CutCaps scD32CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD33Cut_layer0 : gridLayerCurvatureOK
    scD33CutCell scD33CutRoots 1 1 1 scD33CutCaps scD33CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD34Cut_layer0 : gridLayerCurvatureOK
    scD34CutCell scD34CutRoots 1 1 1 scD34CutCaps scD34CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD35Cut_layer0 : gridLayerCurvatureOK
    scD35CutCell scD35CutRoots 1 1 1 scD35CutCaps scD35CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD36Cut_layer0 : gridLayerCurvatureOK
    scD36CutCell scD36CutRoots 1 1 1 scD36CutCaps scD36CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD37Cut_layer0 : gridLayerCurvatureOK
    scD37CutCell scD37CutRoots 1 1 1 scD37CutCaps scD37CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD38Cut_layer0 : gridLayerCurvatureOK
    scD38CutCell scD38CutRoots 1 1 1 scD38CutCaps scD38CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD39Cut_layer0 : gridLayerCurvatureOK
    scD39CutCell scD39CutRoots 1 1 1 scD39CutCaps scD39CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD40Cut_layer0 : gridLayerCurvatureOK
    scD40CutCell scD40CutRoots 1 1 1 scD40CutCaps scD40CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD41Cut_layer0 : gridLayerCurvatureOK
    scD41CutCell scD41CutRoots 1 1 1 scD41CutCaps scD41CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD42Cut_layer0 : gridLayerCurvatureOK
    scD42CutCell scD42CutRoots 1 1 1 scD42CutCaps scD42CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD43Cut_layer0 : gridLayerCurvatureOK
    scD43CutCell scD43CutRoots 1 1 1 scD43CutCaps scD43CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD44Cut_layer0 : gridLayerCurvatureOK
    scD44CutCell scD44CutRoots 1 1 1 scD44CutCaps scD44CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD45Cut_layer0 : gridLayerCurvatureOK
    scD45CutCell scD45CutRoots 1 1 1 scD45CutCaps scD45CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD46Cut_layer0 : gridLayerCurvatureOK
    scD46CutCell scD46CutRoots 1 1 1 scD46CutCaps scD46CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD47Cut_layer0 : gridLayerCurvatureOK
    scD47CutCell scD47CutRoots 1 1 1 scD47CutCaps scD47CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD48Cut_layer0 : gridLayerCurvatureOK
    scD48CutCell scD48CutRoots 1 1 1 scD48CutCaps scD48CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD49Cut_layer0 : gridLayerCurvatureOK
    scD49CutCell scD49CutRoots 1 1 1 scD49CutCaps scD49CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD50Cut_layer0 : gridLayerCurvatureOK
    scD50CutCell scD50CutRoots 1 1 1 scD50CutCaps scD50CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scD51Cut_layer0 : gridLayerCurvatureOK
    scD51CutCell scD51CutRoots 1 1 1 scD51CutCaps scD51CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
