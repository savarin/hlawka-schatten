/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcBandInputs000
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcBandInputs000

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem vcS10Cut_layer0 : gridLayerCurvatureOK
    vcS10CutCell vcS10CutRoots 1 1 1 vcS10CutCaps vcS10CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS11Cut_layer0 : gridLayerCurvatureOK
    vcS11CutCell vcS11CutRoots 1 1 1 vcS11CutCaps vcS11CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS12Cut_layer0 : gridLayerCurvatureOK
    vcS12CutCell vcS12CutRoots 1 1 1 vcS12CutCaps vcS12CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS13Cut_layer0 : gridLayerCurvatureOK
    vcS13CutCell vcS13CutRoots 1 1 1 vcS13CutCaps vcS13CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS14Cut_layer0 : gridLayerCurvatureOK
    vcS14CutCell vcS14CutRoots 1 1 1 vcS14CutCaps vcS14CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS15Cut_layer0 : gridLayerCurvatureOK
    vcS15CutCell vcS15CutRoots 1 1 1 vcS15CutCaps vcS15CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS16Cut_layer0 : gridLayerCurvatureOK
    vcS16CutCell vcS16CutRoots 1 1 1 vcS16CutCaps vcS16CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS17Cut_layer0 : gridLayerCurvatureOK
    vcS17CutCell vcS17CutRoots 1 1 1 vcS17CutCaps vcS17CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS18Cut_layer0 : gridLayerCurvatureOK
    vcS18CutCell vcS18CutRoots 1 1 1 vcS18CutCaps vcS18CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS19Cut_layer0 : gridLayerCurvatureOK
    vcS19CutCell vcS19CutRoots 1 1 1 vcS19CutCaps vcS19CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS110Cut_layer0 : gridLayerCurvatureOK
    vcS110CutCell vcS110CutRoots 1 1 1 vcS110CutCaps vcS110CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS111Cut_layer0 : gridLayerCurvatureOK
    vcS111CutCell vcS111CutRoots 1 1 1 vcS111CutCaps vcS111CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS112Cut_layer0 : gridLayerCurvatureOK
    vcS112CutCell vcS112CutRoots 1 1 1 vcS112CutCaps vcS112CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS113Cut_layer0 : gridLayerCurvatureOK
    vcS113CutCell vcS113CutRoots 1 1 1 vcS113CutCaps vcS113CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS114Cut_layer0 : gridLayerCurvatureOK
    vcS114CutCell vcS114CutRoots 1 1 1 vcS114CutCaps vcS114CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS115Cut_layer0 : gridLayerCurvatureOK
    vcS115CutCell vcS115CutRoots 1 1 1 vcS115CutCaps vcS115CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS116Cut_layer0 : gridLayerCurvatureOK
    vcS116CutCell vcS116CutRoots 1 1 1 vcS116CutCaps vcS116CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS117Cut_layer0 : gridLayerCurvatureOK
    vcS117CutCell vcS117CutRoots 1 1 1 vcS117CutCaps vcS117CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS118Cut_layer0 : gridLayerCurvatureOK
    vcS118CutCell vcS118CutRoots 1 1 1 vcS118CutCaps vcS118CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS119Cut_layer0 : gridLayerCurvatureOK
    vcS119CutCell vcS119CutRoots 1 1 1 vcS119CutCaps vcS119CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS120Cut_layer0 : gridLayerCurvatureOK
    vcS120CutCell vcS120CutRoots 1 1 1 vcS120CutCaps vcS120CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS121Cut_layer0 : gridLayerCurvatureOK
    vcS121CutCell vcS121CutRoots 1 1 1 vcS121CutCaps vcS121CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS122Cut_layer0 : gridLayerCurvatureOK
    vcS122CutCell vcS122CutRoots 1 1 1 vcS122CutCaps vcS122CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS123Cut_layer0 : gridLayerCurvatureOK
    vcS123CutCell vcS123CutRoots 1 1 1 vcS123CutCaps vcS123CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS124Cut_layer0 : gridLayerCurvatureOK
    vcS124CutCell vcS124CutRoots 1 1 1 vcS124CutCaps vcS124CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS125Cut_layer0 : gridLayerCurvatureOK
    vcS125CutCell vcS125CutRoots 1 1 1 vcS125CutCaps vcS125CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS126Cut_layer0 : gridLayerCurvatureOK
    vcS126CutCell vcS126CutRoots 1 1 1 vcS126CutCaps vcS126CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS127Cut_layer0 : gridLayerCurvatureOK
    vcS127CutCell vcS127CutRoots 1 1 1 vcS127CutCaps vcS127CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS128Cut_layer0 : gridLayerCurvatureOK
    vcS128CutCell vcS128CutRoots 1 1 1 vcS128CutCaps vcS128CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS129Cut_layer0 : gridLayerCurvatureOK
    vcS129CutCell vcS129CutRoots 1 1 1 vcS129CutCaps vcS129CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS130Cut_layer0 : gridLayerCurvatureOK
    vcS130CutCell vcS130CutRoots 1 1 1 vcS130CutCaps vcS130CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS131Cut_layer0 : gridLayerCurvatureOK
    vcS131CutCell vcS131CutRoots 1 1 1 vcS131CutCaps vcS131CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
