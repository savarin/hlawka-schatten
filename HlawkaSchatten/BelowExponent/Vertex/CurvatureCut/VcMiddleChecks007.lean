/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs032
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs032

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem vcM39Cut_layer0 : gridLayerCurvatureOK
    vcM39CutCell vcM39CutRoots 1 1 1 vcM39CutCaps vcM39CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM40Cut_layer0 : gridLayerCurvatureOK
    vcM40CutCell vcM40CutRoots 1 1 1 vcM40CutCaps vcM40CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM41Cut_layer0 : gridLayerCurvatureOK
    vcM41CutCell vcM41CutRoots 1 1 1 vcM41CutCaps vcM41CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM42Cut_layer0 : gridLayerCurvatureOK
    vcM42CutCell vcM42CutRoots 1 1 1 vcM42CutCaps vcM42CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM43Cut_layer0 : gridLayerCurvatureOK
    vcM43CutCell vcM43CutRoots 1 1 1 vcM43CutCaps vcM43CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM44Cut_layer0 : gridLayerCurvatureOK
    vcM44CutCell vcM44CutRoots 1 1 1 vcM44CutCaps vcM44CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM45Cut_layer0 : gridLayerCurvatureOK
    vcM45CutCell vcM45CutRoots 1 1 1 vcM45CutCaps vcM45CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM46Cut_layer0 : gridLayerCurvatureOK
    vcM46CutCell vcM46CutRoots 1 1 1 vcM46CutCaps vcM46CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM47Cut_layer0 : gridLayerCurvatureOK
    vcM47CutCell vcM47CutRoots 1 1 1 vcM47CutCaps vcM47CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM48Cut_layer0 : gridLayerCurvatureOK
    vcM48CutCell vcM48CutRoots 1 1 1 vcM48CutCaps vcM48CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM49Cut_layer0 : gridLayerCurvatureOK
    vcM49CutCell vcM49CutRoots 1 1 1 vcM49CutCaps vcM49CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM50Cut_layer0 : gridLayerCurvatureOK
    vcM50CutCell vcM50CutRoots 1 1 1 vcM50CutCaps vcM50CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM51Cut_layer0 : gridLayerCurvatureOK
    vcM51CutCell vcM51CutRoots 1 1 1 vcM51CutCaps vcM51CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM52Cut_layer0 : gridLayerCurvatureOK
    vcM52CutCell vcM52CutRoots 1 1 1 vcM52CutCaps vcM52CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM53Cut_layer0 : gridLayerCurvatureOK
    vcM53CutCell vcM53CutRoots 1 1 1 vcM53CutCaps vcM53CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM54Cut_layer0 : gridLayerCurvatureOK
    vcM54CutCell vcM54CutRoots 1 1 1 vcM54CutCaps vcM54CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM55Cut_layer0 : gridLayerCurvatureOK
    vcM55CutCell vcM55CutRoots 1 1 1 vcM55CutCaps vcM55CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM56Cut_layer0 : gridLayerCurvatureOK
    vcM56CutCell vcM56CutRoots 1 1 1 vcM56CutCaps vcM56CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM57Cut_layer0 : gridLayerCurvatureOK
    vcM57CutCell vcM57CutRoots 1 1 1 vcM57CutCaps vcM57CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM64Cut_layer0 : gridLayerCurvatureOK
    vcM64CutCell vcM64CutRoots 2 2 1 vcM64CutCaps vcM64CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM64Cut_layer1 : gridLayerCurvatureOK
    vcM64CutCell vcM64CutRoots 2 2 1 vcM64CutCaps vcM64CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM65Cut_layer0 : gridLayerCurvatureOK
    vcM65CutCell vcM65CutRoots 2 2 1 vcM65CutCaps vcM65CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM65Cut_layer1 : gridLayerCurvatureOK
    vcM65CutCell vcM65CutRoots 2 2 1 vcM65CutCaps vcM65CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM66Cut_layer0 : gridLayerCurvatureOK
    vcM66CutCell vcM66CutRoots 1 1 1 vcM66CutCaps vcM66CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM67Cut_layer0 : gridLayerCurvatureOK
    vcM67CutCell vcM67CutRoots 1 1 1 vcM67CutCaps vcM67CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM68Cut_layer0 : gridLayerCurvatureOK
    vcM68CutCell vcM68CutRoots 1 1 1 vcM68CutCaps vcM68CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM69Cut_layer0 : gridLayerCurvatureOK
    vcM69CutCell vcM69CutRoots 1 1 1 vcM69CutCaps vcM69CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM70Cut_layer0 : gridLayerCurvatureOK
    vcM70CutCell vcM70CutRoots 1 1 1 vcM70CutCaps vcM70CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
