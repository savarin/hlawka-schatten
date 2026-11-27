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

theorem vcM25Cut_layer0 : gridLayerCurvatureOK
    vcM25CutCell vcM25CutRoots 1 1 1 vcM25CutCaps vcM25CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM26Cut_layer0 : gridLayerCurvatureOK
    vcM26CutCell vcM26CutRoots 1 1 1 vcM26CutCaps vcM26CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM27Cut_layer0 : gridLayerCurvatureOK
    vcM27CutCell vcM27CutRoots 1 1 1 vcM27CutCaps vcM27CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem vcM30Cut_layer0 : gridLayerCurvatureOK
    vcM30CutCell vcM30CutRoots 8 8 2 vcM30CutCaps vcM30CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
