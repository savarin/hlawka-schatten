/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs384
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideInputs384

/-! Kernel arithmetic proofs for the closed curvature subcells. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem scE78Cut_layer0 : gridLayerCurvatureOK
    scE78CutCell scE78CutRoots 1 1 1 scE78CutCaps scE78CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE79Cut_layer0 : gridLayerCurvatureOK
    scE79CutCell scE79CutRoots 1 1 1 scE79CutCaps scE79CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE80Cut_layer0 : gridLayerCurvatureOK
    scE80CutCell scE80CutRoots 1 1 1 scE80CutCaps scE80CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE81Cut_layer0 : gridLayerCurvatureOK
    scE81CutCell scE81CutRoots 1 1 1 scE81CutCaps scE81CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE82Cut_layer0 : gridLayerCurvatureOK
    scE82CutCell scE82CutRoots 1 1 1 scE82CutCaps scE82CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE83Cut_layer0 : gridLayerCurvatureOK
    scE83CutCell scE83CutRoots 1 1 1 scE83CutCaps scE83CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE84Cut_layer0 : gridLayerCurvatureOK
    scE84CutCell scE84CutRoots 1 1 1 scE84CutCaps scE84CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE85Cut_layer0 : gridLayerCurvatureOK
    scE85CutCell scE85CutRoots 1 1 1 scE85CutCaps scE85CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE86Cut_layer0 : gridLayerCurvatureOK
    scE86CutCell scE86CutRoots 1 1 1 scE86CutCaps scE86CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE87Cut_layer0 : gridLayerCurvatureOK
    scE87CutCell scE87CutRoots 1 1 1 scE87CutCaps scE87CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE88Cut_layer0 : gridLayerCurvatureOK
    scE88CutCell scE88CutRoots 1 1 1 scE88CutCaps scE88CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE89Cut_layer0 : gridLayerCurvatureOK
    scE89CutCell scE89CutRoots 1 1 1 scE89CutCaps scE89CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE90Cut_layer0 : gridLayerCurvatureOK
    scE90CutCell scE90CutRoots 1 1 1 scE90CutCaps scE90CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE91Cut_layer0 : gridLayerCurvatureOK
    scE91CutCell scE91CutRoots 1 1 1 scE91CutCaps scE91CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE92Cut_layer0 : gridLayerCurvatureOK
    scE92CutCell scE92CutRoots 1 1 1 scE92CutCaps scE92CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE93Cut_layer0 : gridLayerCurvatureOK
    scE93CutCell scE93CutRoots 1 1 1 scE93CutCaps scE93CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE94Cut_layer0 : gridLayerCurvatureOK
    scE94CutCell scE94CutRoots 1 1 1 scE94CutCaps scE94CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE95Cut_layer0 : gridLayerCurvatureOK
    scE95CutCell scE95CutRoots 1 1 1 scE95CutCaps scE95CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE96Cut_layer0 : gridLayerCurvatureOK
    scE96CutCell scE96CutRoots 1 1 1 scE96CutCaps scE96CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE97Cut_layer0 : gridLayerCurvatureOK
    scE97CutCell scE97CutRoots 1 1 1 scE97CutCaps scE97CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE98Cut_layer0 : gridLayerCurvatureOK
    scE98CutCell scE98CutRoots 1 1 1 scE98CutCaps scE98CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE99Cut_layer0 : gridLayerCurvatureOK
    scE99CutCell scE99CutRoots 1 1 1 scE99CutCaps scE99CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE100Cut_layer0 : gridLayerCurvatureOK
    scE100CutCell scE100CutRoots 1 1 1 scE100CutCaps scE100CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE101Cut_layer0 : gridLayerCurvatureOK
    scE101CutCell scE101CutRoots 1 1 1 scE101CutCaps scE101CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE102Cut_layer0 : gridLayerCurvatureOK
    scE102CutCell scE102CutRoots 1 1 1 scE102CutCaps scE102CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE103Cut_layer0 : gridLayerCurvatureOK
    scE103CutCell scE103CutRoots 1 1 1 scE103CutCaps scE103CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE104Cut_layer0 : gridLayerCurvatureOK
    scE104CutCell scE104CutRoots 1 1 1 scE104CutCaps scE104CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE105Cut_layer0 : gridLayerCurvatureOK
    scE105CutCell scE105CutRoots 1 1 1 scE105CutCaps scE105CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE106Cut_layer0 : gridLayerCurvatureOK
    scE106CutCell scE106CutRoots 1 1 1 scE106CutCaps scE106CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE107Cut_layer0 : gridLayerCurvatureOK
    scE107CutCell scE107CutRoots 1 1 1 scE107CutCaps scE107CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE108Cut_layer0 : gridLayerCurvatureOK
    scE108CutCell scE108CutRoots 1 1 1 scE108CutCaps scE108CutWeightFloor 0 = true := by
  replay_curvature_layer

theorem scE109Cut_layer0 : gridLayerCurvatureOK
    scE109CutCell scE109CutRoots 1 1 1 scE109CutCaps scE109CutWeightFloor 0 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
