/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcM58Pilot.Inputs
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcM58Pilot.Inputs
meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureReplay

/-! Two independently checked curvature layers of the VC-M 58 pilot. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem vcM58Pilot_layer14 : gridLayerCurvatureOK
    vcM58Cell vcM58Roots 16 18 1 vcM58PilotCaps vcM58PilotFloor 14 = true := by
  replay_curvature_layer

theorem vcM58Pilot_layer15 : gridLayerCurvatureOK
    vcM58Cell vcM58Roots 16 18 1 vcM58PilotCaps vcM58PilotFloor 15 = true := by
  replay_curvature_layer


end HlawkaSchatten.BelowExponent.Vertex
