/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs064
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs096
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs064
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleInputs096

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem vcM101Cut_layer0 : gridLayerCurvatureOK
    vcM101CutCell vcM101CutRoots 1 1 1 vcM101CutCaps vcM101CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM102Cut_layer0 : gridLayerCurvatureOK
    vcM102CutCell vcM102CutRoots 1 1 1 vcM102CutCaps vcM102CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM103Cut_layer0 : gridLayerCurvatureOK
    vcM103CutCell vcM103CutRoots 1 1 1 vcM103CutCaps vcM103CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM104Cut_layer0 : gridLayerCurvatureOK
    vcM104CutCell vcM104CutRoots 1 1 1 vcM104CutCaps vcM104CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM105Cut_layer0 : gridLayerCurvatureOK
    vcM105CutCell vcM105CutRoots 1 1 1 vcM105CutCaps vcM105CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM106Cut_layer0 : gridLayerCurvatureOK
    vcM106CutCell vcM106CutRoots 1 1 1 vcM106CutCaps vcM106CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM107Cut_layer0 : gridLayerCurvatureOK
    vcM107CutCell vcM107CutRoots 1 1 1 vcM107CutCaps vcM107CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM108Cut_layer0 : gridLayerCurvatureOK
    vcM108CutCell vcM108CutRoots 1 1 1 vcM108CutCaps vcM108CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM109Cut_layer0 : gridLayerCurvatureOK
    vcM109CutCell vcM109CutRoots 1 1 1 vcM109CutCaps vcM109CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM110Cut_layer0 : gridLayerCurvatureOK
    vcM110CutCell vcM110CutRoots 1 1 1 vcM110CutCaps vcM110CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM111Cut_layer0 : gridLayerCurvatureOK
    vcM111CutCell vcM111CutRoots 1 1 1 vcM111CutCaps vcM111CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM114Cut_layer0 : gridLayerCurvatureOK
    vcM114CutCell vcM114CutRoots 2 2 1 vcM114CutCaps vcM114CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM114Cut_layer1 : gridLayerCurvatureOK
    vcM114CutCell vcM114CutRoots 2 2 1 vcM114CutCaps vcM114CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM115Cut_layer0 : gridLayerCurvatureOK
    vcM115CutCell vcM115CutRoots 2 2 1 vcM115CutCaps vcM115CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM115Cut_layer1 : gridLayerCurvatureOK
    vcM115CutCell vcM115CutRoots 2 2 1 vcM115CutCaps vcM115CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM116Cut_layer0 : gridLayerCurvatureOK
    vcM116CutCell vcM116CutRoots 1 1 1 vcM116CutCaps vcM116CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM117Cut_layer0 : gridLayerCurvatureOK
    vcM117CutCell vcM117CutRoots 2 2 1 vcM117CutCaps vcM117CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM117Cut_layer1 : gridLayerCurvatureOK
    vcM117CutCell vcM117CutRoots 2 2 1 vcM117CutCaps vcM117CutWeightFloor 1 = true := by
  replay_curvature_layer

theorem vcM118Cut_layer0 : gridLayerCurvatureOK
    vcM118CutCell vcM118CutRoots 1 1 1 vcM118CutCaps vcM118CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM119Cut_layer0 : gridLayerCurvatureOK
    vcM119CutCell vcM119CutRoots 1 1 1 vcM119CutCaps vcM119CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM120Cut_layer0 : gridLayerCurvatureOK
    vcM120CutCell vcM120CutRoots 1 1 1 vcM120CutCaps vcM120CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM121Cut_layer0 : gridLayerCurvatureOK
    vcM121CutCell vcM121CutRoots 1 1 1 vcM121CutCaps vcM121CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM122Cut_layer0 : gridLayerCurvatureOK
    vcM122CutCell vcM122CutRoots 1 1 1 vcM122CutCaps vcM122CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM123Cut_layer0 : gridLayerCurvatureOK
    vcM123CutCell vcM123CutRoots 1 1 1 vcM123CutCaps vcM123CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM124Cut_layer0 : gridLayerCurvatureOK
    vcM124CutCell vcM124CutRoots 1 1 1 vcM124CutCaps vcM124CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM125Cut_layer0 : gridLayerCurvatureOK
    vcM125CutCell vcM125CutRoots 1 1 1 vcM125CutCaps vcM125CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
