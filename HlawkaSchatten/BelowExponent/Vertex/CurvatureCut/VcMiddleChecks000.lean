/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs000
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs000

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem vcM2Cut_layer0 : gridLayerCurvatureOK
    vcM2CutCell vcM2CutRoots 2 2 2 vcM2CutCaps vcM2CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM2Cut_layer1 : gridLayerCurvatureOK
    vcM2CutCell vcM2CutRoots 2 2 2 vcM2CutCaps vcM2CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM4Cut_layer0 : gridLayerCurvatureOK
    vcM4CutCell vcM4CutRoots 1 1 1 vcM4CutCaps vcM4CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM5Cut_layer0 : gridLayerCurvatureOK
    vcM5CutCell vcM5CutRoots 2 2 1 vcM5CutCaps vcM5CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM5Cut_layer1 : gridLayerCurvatureOK
    vcM5CutCell vcM5CutRoots 2 2 1 vcM5CutCaps vcM5CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM6Cut_layer0 : gridLayerCurvatureOK
    vcM6CutCell vcM6CutRoots 1 1 1 vcM6CutCaps vcM6CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM7Cut_layer0 : gridLayerCurvatureOK
    vcM7CutCell vcM7CutRoots 1 1 1 vcM7CutCaps vcM7CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM8Cut_layer0 : gridLayerCurvatureOK
    vcM8CutCell vcM8CutRoots 1 1 1 vcM8CutCaps vcM8CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM9Cut_layer0 : gridLayerCurvatureOK
    vcM9CutCell vcM9CutRoots 1 1 1 vcM9CutCaps vcM9CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM10Cut_layer0 : gridLayerCurvatureOK
    vcM10CutCell vcM10CutRoots 1 1 1 vcM10CutCaps vcM10CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM11Cut_layer0 : gridLayerCurvatureOK
    vcM11CutCell vcM11CutRoots 1 1 1 vcM11CutCaps vcM11CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM12Cut_layer0 : gridLayerCurvatureOK
    vcM12CutCell vcM12CutRoots 1 1 1 vcM12CutCaps vcM12CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM13Cut_layer0 : gridLayerCurvatureOK
    vcM13CutCell vcM13CutRoots 1 1 1 vcM13CutCaps vcM13CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM14Cut_layer0 : gridLayerCurvatureOK
    vcM14CutCell vcM14CutRoots 1 1 1 vcM14CutCaps vcM14CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM15Cut_layer0 : gridLayerCurvatureOK
    vcM15CutCell vcM15CutRoots 1 1 1 vcM15CutCaps vcM15CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM16Cut_layer0 : gridLayerCurvatureOK
    vcM16CutCell vcM16CutRoots 1 1 1 vcM16CutCaps vcM16CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM17Cut_layer0 : gridLayerCurvatureOK
    vcM17CutCell vcM17CutRoots 1 1 1 vcM17CutCaps vcM17CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM18Cut_layer0 : gridLayerCurvatureOK
    vcM18CutCell vcM18CutRoots 1 1 1 vcM18CutCaps vcM18CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM19Cut_layer0 : gridLayerCurvatureOK
    vcM19CutCell vcM19CutRoots 1 1 1 vcM19CutCaps vcM19CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM20Cut_layer0 : gridLayerCurvatureOK
    vcM20CutCell vcM20CutRoots 1 1 1 vcM20CutCaps vcM20CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM21Cut_layer0 : gridLayerCurvatureOK
    vcM21CutCell vcM21CutRoots 1 1 1 vcM21CutCaps vcM21CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM22Cut_layer0 : gridLayerCurvatureOK
    vcM22CutCell vcM22CutRoots 1 1 1 vcM22CutCaps vcM22CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM23Cut_layer0 : gridLayerCurvatureOK
    vcM23CutCell vcM23CutRoots 1 1 1 vcM23CutCaps vcM23CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM24Cut_layer0 : gridLayerCurvatureOK
    vcM24CutCell vcM24CutRoots 1 1 1 vcM24CutCaps vcM24CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
