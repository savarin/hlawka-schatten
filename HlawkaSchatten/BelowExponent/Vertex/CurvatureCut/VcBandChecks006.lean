/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcBandInputs192
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcBandInputs192

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem vcS1192Cut_layer0 : gridLayerCurvatureOK
    vcS1192CutCell vcS1192CutRoots 1 1 1 vcS1192CutCaps vcS1192CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1193Cut_layer0 : gridLayerCurvatureOK
    vcS1193CutCell vcS1193CutRoots 1 1 1 vcS1193CutCaps vcS1193CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1194Cut_layer0 : gridLayerCurvatureOK
    vcS1194CutCell vcS1194CutRoots 1 1 1 vcS1194CutCaps vcS1194CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1195Cut_layer0 : gridLayerCurvatureOK
    vcS1195CutCell vcS1195CutRoots 1 1 1 vcS1195CutCaps vcS1195CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1196Cut_layer0 : gridLayerCurvatureOK
    vcS1196CutCell vcS1196CutRoots 1 1 1 vcS1196CutCaps vcS1196CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1197Cut_layer0 : gridLayerCurvatureOK
    vcS1197CutCell vcS1197CutRoots 1 1 1 vcS1197CutCaps vcS1197CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1198Cut_layer0 : gridLayerCurvatureOK
    vcS1198CutCell vcS1198CutRoots 1 1 1 vcS1198CutCaps vcS1198CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1199Cut_layer0 : gridLayerCurvatureOK
    vcS1199CutCell vcS1199CutRoots 1 1 1 vcS1199CutCaps vcS1199CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1200Cut_layer0 : gridLayerCurvatureOK
    vcS1200CutCell vcS1200CutRoots 1 1 1 vcS1200CutCaps vcS1200CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1201Cut_layer0 : gridLayerCurvatureOK
    vcS1201CutCell vcS1201CutRoots 1 1 1 vcS1201CutCaps vcS1201CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1202Cut_layer0 : gridLayerCurvatureOK
    vcS1202CutCell vcS1202CutRoots 1 1 1 vcS1202CutCaps vcS1202CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1203Cut_layer0 : gridLayerCurvatureOK
    vcS1203CutCell vcS1203CutRoots 1 1 1 vcS1203CutCaps vcS1203CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1204Cut_layer0 : gridLayerCurvatureOK
    vcS1204CutCell vcS1204CutRoots 1 1 1 vcS1204CutCaps vcS1204CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1205Cut_layer0 : gridLayerCurvatureOK
    vcS1205CutCell vcS1205CutRoots 1 1 1 vcS1205CutCaps vcS1205CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1206Cut_layer0 : gridLayerCurvatureOK
    vcS1206CutCell vcS1206CutRoots 1 1 1 vcS1206CutCaps vcS1206CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1207Cut_layer0 : gridLayerCurvatureOK
    vcS1207CutCell vcS1207CutRoots 1 1 1 vcS1207CutCaps vcS1207CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1208Cut_layer0 : gridLayerCurvatureOK
    vcS1208CutCell vcS1208CutRoots 1 1 1 vcS1208CutCaps vcS1208CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1209Cut_layer0 : gridLayerCurvatureOK
    vcS1209CutCell vcS1209CutRoots 1 1 1 vcS1209CutCaps vcS1209CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1210Cut_layer0 : gridLayerCurvatureOK
    vcS1210CutCell vcS1210CutRoots 1 1 1 vcS1210CutCaps vcS1210CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcS1211Cut_layer0 : gridLayerCurvatureOK
    vcS1211CutCell vcS1211CutRoots 1 1 1 vcS1211CutCaps vcS1211CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
