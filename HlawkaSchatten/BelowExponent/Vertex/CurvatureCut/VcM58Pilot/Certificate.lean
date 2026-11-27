/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcM58Pilot.Layer00
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcM58Pilot.Layer02
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcM58Pilot.Layer04
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcM58Pilot.Layer06
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcM58Pilot.Layer08
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcM58Pilot.Layer10
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcM58Pilot.Layer12
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcM58Pilot.Layer14
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCertificates
meta import Mathlib.Tactic.FinCases

/-! The checked 288-subcell curvature certificate on the original VC-M 58 box. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 12000

theorem vcM58Pilot_layer_checks (i : Fin 16) : gridLayerCurvatureOK
    vcM58Cell vcM58Roots 16 18 1 vcM58PilotCaps vcM58PilotFloor i = true := by
  fin_cases i
  · exact vcM58Pilot_layer0
  · exact vcM58Pilot_layer1
  · exact vcM58Pilot_layer2
  · exact vcM58Pilot_layer3
  · exact vcM58Pilot_layer4
  · exact vcM58Pilot_layer5
  · exact vcM58Pilot_layer6
  · exact vcM58Pilot_layer7
  · exact vcM58Pilot_layer8
  · exact vcM58Pilot_layer9
  · exact vcM58Pilot_layer10
  · exact vcM58Pilot_layer11
  · exact vcM58Pilot_layer12
  · exact vcM58Pilot_layer13
  · exact vcM58Pilot_layer14
  · exact vcM58Pilot_layer15

def vcM58PilotCertificate : CurvatureCellCertificate :=
  CurvatureCellCertificate.of_layer_checks (c := vcM58Cell) (roots := vcM58Roots)
    (na := 16) (nb := 18) (nη := 1) (caps := vcM58PilotCaps) (weightFloor := vcM58PilotFloor)
    (margins := vcM58Margins) vcM58_roots_ok vcM58Pilot_layer_checks (by decide +kernel)
    vcM58Pilot_caps_nonneg vcM58Pilot_margins (by decide) (by decide +kernel)

end HlawkaSchatten.BelowExponent.Vertex
