/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCertificates
public import HlawkaSchatten.BelowExponent.Vertex.SideConeParameterGrid
meta import Mathlib.Tactic.FinCases
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks000
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks001
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks002
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks003
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks004
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks005
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks006
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks007
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks008
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks009
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks010
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks011
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks012
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks013
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks014
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.SideChecks015

/-! Checked curvature and weights on the same closed parameter grid. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def scCutCurvatureCertificates000 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scS0CutCell) (roots := scS0CutRoots)
    (caps := scS0CutCaps) (weightFloor := scS0CutWeightFloor) (margins := scS0CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS0Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS0Cut_layer0)
    (by decide +kernel) scS0Cut_caps_nonneg scS0Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS1CutCell) (roots := scS1CutRoots)
    (caps := scS1CutCaps) (weightFloor := scS1CutWeightFloor) (margins := scS1CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS1Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS1Cut_layer0)
    (by decide +kernel) scS1Cut_caps_nonneg scS1Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS2CutCell) (roots := scS2CutRoots)
    (caps := scS2CutCaps) (weightFloor := scS2CutWeightFloor) (margins := scS2CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS2Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS2Cut_layer0)
    (by decide +kernel) scS2Cut_caps_nonneg scS2Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS3CutCell) (roots := scS3CutRoots)
    (caps := scS3CutCaps) (weightFloor := scS3CutWeightFloor) (margins := scS3CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS3Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS3Cut_layer0)
    (by decide +kernel) scS3Cut_caps_nonneg scS3Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS4CutCell) (roots := scS4CutRoots)
    (caps := scS4CutCaps) (weightFloor := scS4CutWeightFloor) (margins := scS4CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS4Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS4Cut_layer0)
    (by decide +kernel) scS4Cut_caps_nonneg scS4Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS5CutCell) (roots := scS5CutRoots)
    (caps := scS5CutCaps) (weightFloor := scS5CutWeightFloor) (margins := scS5CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS5Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS5Cut_layer0)
    (by decide +kernel) scS5Cut_caps_nonneg scS5Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS6CutCell) (roots := scS6CutRoots)
    (caps := scS6CutCaps) (weightFloor := scS6CutWeightFloor) (margins := scS6CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS6Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS6Cut_layer0)
    (by decide +kernel) scS6Cut_caps_nonneg scS6Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS7CutCell) (roots := scS7CutRoots)
    (caps := scS7CutCaps) (weightFloor := scS7CutWeightFloor) (margins := scS7CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS7Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS7Cut_layer0)
    (by decide +kernel) scS7Cut_caps_nonneg scS7Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS8CutCell) (roots := scS8CutRoots)
    (caps := scS8CutCaps) (weightFloor := scS8CutWeightFloor) (margins := scS8CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS8Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS8Cut_layer0)
    (by decide +kernel) scS8Cut_caps_nonneg scS8Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS9CutCell) (roots := scS9CutRoots)
    (caps := scS9CutCaps) (weightFloor := scS9CutWeightFloor) (margins := scS9CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS9Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS9Cut_layer0)
    (by decide +kernel) scS9Cut_caps_nonneg scS9Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS10CutCell) (roots := scS10CutRoots)
    (caps := scS10CutCaps) (weightFloor := scS10CutWeightFloor) (margins := scS10CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS10Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS10Cut_layer0)
    (by decide +kernel) scS10Cut_caps_nonneg scS10Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS11CutCell) (roots := scS11CutRoots)
    (caps := scS11CutCaps) (weightFloor := scS11CutWeightFloor) (margins := scS11CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS11Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS11Cut_layer0)
    (by decide +kernel) scS11Cut_caps_nonneg scS11Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS12CutCell) (roots := scS12CutRoots)
    (caps := scS12CutCaps) (weightFloor := scS12CutWeightFloor) (margins := scS12CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS12Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS12Cut_layer0)
    (by decide +kernel) scS12Cut_caps_nonneg scS12Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS13CutCell) (roots := scS13CutRoots)
    (caps := scS13CutCaps) (weightFloor := scS13CutWeightFloor) (margins := scS13CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS13Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS13Cut_layer0)
    (by decide +kernel) scS13Cut_caps_nonneg scS13Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS14CutCell) (roots := scS14CutRoots)
    (caps := scS14CutCaps) (weightFloor := scS14CutWeightFloor) (margins := scS14CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS14Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS14Cut_layer0)
    (by decide +kernel) scS14Cut_caps_nonneg scS14Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS15CutCell) (roots := scS15CutRoots)
    (caps := scS15CutCaps) (weightFloor := scS15CutWeightFloor) (margins := scS15CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS15Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS15Cut_layer0)
    (by decide +kernel) scS15Cut_caps_nonneg scS15Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS16CutCell) (roots := scS16CutRoots)
    (caps := scS16CutCaps) (weightFloor := scS16CutWeightFloor) (margins := scS16CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS16Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS16Cut_layer0)
    (by decide +kernel) scS16Cut_caps_nonneg scS16Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS17CutCell) (roots := scS17CutRoots)
    (caps := scS17CutCaps) (weightFloor := scS17CutWeightFloor) (margins := scS17CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS17Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS17Cut_layer0)
    (by decide +kernel) scS17Cut_caps_nonneg scS17Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS18CutCell) (roots := scS18CutRoots)
    (caps := scS18CutCaps) (weightFloor := scS18CutWeightFloor) (margins := scS18CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS18Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS18Cut_layer0)
    (by decide +kernel) scS18Cut_caps_nonneg scS18Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS19CutCell) (roots := scS19CutRoots)
    (caps := scS19CutCaps) (weightFloor := scS19CutWeightFloor) (margins := scS19CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS19Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS19Cut_layer0)
    (by decide +kernel) scS19Cut_caps_nonneg scS19Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS20CutCell) (roots := scS20CutRoots)
    (caps := scS20CutCaps) (weightFloor := scS20CutWeightFloor) (margins := scS20CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS20Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS20Cut_layer0)
    (by decide +kernel) scS20Cut_caps_nonneg scS20Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS21CutCell) (roots := scS21CutRoots)
    (caps := scS21CutCaps) (weightFloor := scS21CutWeightFloor) (margins := scS21CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS21Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS21Cut_layer0)
    (by decide +kernel) scS21Cut_caps_nonneg scS21Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS22CutCell) (roots := scS22CutRoots)
    (caps := scS22CutCaps) (weightFloor := scS22CutWeightFloor) (margins := scS22CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS22Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS22Cut_layer0)
    (by decide +kernel) scS22Cut_caps_nonneg scS22Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS23CutCell) (roots := scS23CutRoots)
    (caps := scS23CutCaps) (weightFloor := scS23CutWeightFloor) (margins := scS23CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS23Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS23Cut_layer0)
    (by decide +kernel) scS23Cut_caps_nonneg scS23Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS24CutCell) (roots := scS24CutRoots)
    (caps := scS24CutCaps) (weightFloor := scS24CutWeightFloor) (margins := scS24CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS24Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS24Cut_layer0)
    (by decide +kernel) scS24Cut_caps_nonneg scS24Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS25CutCell) (roots := scS25CutRoots)
    (caps := scS25CutCaps) (weightFloor := scS25CutWeightFloor) (margins := scS25CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS25Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS25Cut_layer0)
    (by decide +kernel) scS25Cut_caps_nonneg scS25Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS26CutCell) (roots := scS26CutRoots)
    (caps := scS26CutCaps) (weightFloor := scS26CutWeightFloor) (margins := scS26CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS26Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS26Cut_layer0)
    (by decide +kernel) scS26Cut_caps_nonneg scS26Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS27CutCell) (roots := scS27CutRoots)
    (caps := scS27CutCaps) (weightFloor := scS27CutWeightFloor) (margins := scS27CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS27Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS27Cut_layer0)
    (by decide +kernel) scS27Cut_caps_nonneg scS27Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS28CutCell) (roots := scS28CutRoots)
    (caps := scS28CutCaps) (weightFloor := scS28CutWeightFloor) (margins := scS28CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS28Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS28Cut_layer0)
    (by decide +kernel) scS28Cut_caps_nonneg scS28Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS29CutCell) (roots := scS29CutRoots)
    (caps := scS29CutCaps) (weightFloor := scS29CutWeightFloor) (margins := scS29CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS29Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS29Cut_layer0)
    (by decide +kernel) scS29Cut_caps_nonneg scS29Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS30CutCell) (roots := scS30CutRoots)
    (caps := scS30CutCaps) (weightFloor := scS30CutWeightFloor) (margins := scS30CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS30Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS30Cut_layer0)
    (by decide +kernel) scS30Cut_caps_nonneg scS30Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS31CutCell) (roots := scS31CutRoots)
    (caps := scS31CutCaps) (weightFloor := scS31CutWeightFloor) (margins := scS31CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS31Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS31Cut_layer0)
    (by decide +kernel) scS31Cut_caps_nonneg scS31Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates032 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scS32CutCell) (roots := scS32CutRoots)
    (caps := scS32CutCaps) (weightFloor := scS32CutWeightFloor) (margins := scS32CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS32Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS32Cut_layer0)
    (by decide +kernel) scS32Cut_caps_nonneg scS32Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS33CutCell) (roots := scS33CutRoots)
    (caps := scS33CutCaps) (weightFloor := scS33CutWeightFloor) (margins := scS33CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS33Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS33Cut_layer0)
    (by decide +kernel) scS33Cut_caps_nonneg scS33Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS34CutCell) (roots := scS34CutRoots)
    (caps := scS34CutCaps) (weightFloor := scS34CutWeightFloor) (margins := scS34CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS34Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS34Cut_layer0)
    (by decide +kernel) scS34Cut_caps_nonneg scS34Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS35CutCell) (roots := scS35CutRoots)
    (caps := scS35CutCaps) (weightFloor := scS35CutWeightFloor) (margins := scS35CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS35Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS35Cut_layer0)
    (by decide +kernel) scS35Cut_caps_nonneg scS35Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS36CutCell) (roots := scS36CutRoots)
    (caps := scS36CutCaps) (weightFloor := scS36CutWeightFloor) (margins := scS36CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS36Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS36Cut_layer0)
    (by decide +kernel) scS36Cut_caps_nonneg scS36Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS37CutCell) (roots := scS37CutRoots)
    (caps := scS37CutCaps) (weightFloor := scS37CutWeightFloor) (margins := scS37CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS37Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS37Cut_layer0)
    (by decide +kernel) scS37Cut_caps_nonneg scS37Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS38CutCell) (roots := scS38CutRoots)
    (caps := scS38CutCaps) (weightFloor := scS38CutWeightFloor) (margins := scS38CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS38Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS38Cut_layer0)
    (by decide +kernel) scS38Cut_caps_nonneg scS38Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS39CutCell) (roots := scS39CutRoots)
    (caps := scS39CutCaps) (weightFloor := scS39CutWeightFloor) (margins := scS39CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS39Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS39Cut_layer0)
    (by decide +kernel) scS39Cut_caps_nonneg scS39Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS40CutCell) (roots := scS40CutRoots)
    (caps := scS40CutCaps) (weightFloor := scS40CutWeightFloor) (margins := scS40CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS40Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS40Cut_layer0)
    (by decide +kernel) scS40Cut_caps_nonneg scS40Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS41CutCell) (roots := scS41CutRoots)
    (caps := scS41CutCaps) (weightFloor := scS41CutWeightFloor) (margins := scS41CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS41Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS41Cut_layer0)
    (by decide +kernel) scS41Cut_caps_nonneg scS41Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS42CutCell) (roots := scS42CutRoots)
    (caps := scS42CutCaps) (weightFloor := scS42CutWeightFloor) (margins := scS42CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS42Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS42Cut_layer0)
    (by decide +kernel) scS42Cut_caps_nonneg scS42Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS43CutCell) (roots := scS43CutRoots)
    (caps := scS43CutCaps) (weightFloor := scS43CutWeightFloor) (margins := scS43CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS43Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS43Cut_layer0)
    (by decide +kernel) scS43Cut_caps_nonneg scS43Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS44CutCell) (roots := scS44CutRoots)
    (caps := scS44CutCaps) (weightFloor := scS44CutWeightFloor) (margins := scS44CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS44Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS44Cut_layer0)
    (by decide +kernel) scS44Cut_caps_nonneg scS44Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS45CutCell) (roots := scS45CutRoots)
    (caps := scS45CutCaps) (weightFloor := scS45CutWeightFloor) (margins := scS45CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS45Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS45Cut_layer0)
    (by decide +kernel) scS45Cut_caps_nonneg scS45Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS46CutCell) (roots := scS46CutRoots)
    (caps := scS46CutCaps) (weightFloor := scS46CutWeightFloor) (margins := scS46CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS46Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS46Cut_layer0)
    (by decide +kernel) scS46Cut_caps_nonneg scS46Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS47CutCell) (roots := scS47CutRoots)
    (caps := scS47CutCaps) (weightFloor := scS47CutWeightFloor) (margins := scS47CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS47Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS47Cut_layer0)
    (by decide +kernel) scS47Cut_caps_nonneg scS47Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS48CutCell) (roots := scS48CutRoots)
    (caps := scS48CutCaps) (weightFloor := scS48CutWeightFloor) (margins := scS48CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS48Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS48Cut_layer0)
    (by decide +kernel) scS48Cut_caps_nonneg scS48Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS49CutCell) (roots := scS49CutRoots)
    (caps := scS49CutCaps) (weightFloor := scS49CutWeightFloor) (margins := scS49CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS49Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS49Cut_layer0)
    (by decide +kernel) scS49Cut_caps_nonneg scS49Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS50CutCell) (roots := scS50CutRoots)
    (caps := scS50CutCaps) (weightFloor := scS50CutWeightFloor) (margins := scS50CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS50Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS50Cut_layer0)
    (by decide +kernel) scS50Cut_caps_nonneg scS50Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS51CutCell) (roots := scS51CutRoots)
    (caps := scS51CutCaps) (weightFloor := scS51CutWeightFloor) (margins := scS51CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS51Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS51Cut_layer0)
    (by decide +kernel) scS51Cut_caps_nonneg scS51Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS52CutCell) (roots := scS52CutRoots)
    (caps := scS52CutCaps) (weightFloor := scS52CutWeightFloor) (margins := scS52CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS52Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS52Cut_layer0)
    (by decide +kernel) scS52Cut_caps_nonneg scS52Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS53CutCell) (roots := scS53CutRoots)
    (caps := scS53CutCaps) (weightFloor := scS53CutWeightFloor) (margins := scS53CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS53Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS53Cut_layer0)
    (by decide +kernel) scS53Cut_caps_nonneg scS53Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS54CutCell) (roots := scS54CutRoots)
    (caps := scS54CutCaps) (weightFloor := scS54CutWeightFloor) (margins := scS54CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS54Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS54Cut_layer0)
    (by decide +kernel) scS54Cut_caps_nonneg scS54Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS55CutCell) (roots := scS55CutRoots)
    (caps := scS55CutCaps) (weightFloor := scS55CutWeightFloor) (margins := scS55CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS55Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS55Cut_layer0)
    (by decide +kernel) scS55Cut_caps_nonneg scS55Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS56CutCell) (roots := scS56CutRoots)
    (caps := scS56CutCaps) (weightFloor := scS56CutWeightFloor) (margins := scS56CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS56Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS56Cut_layer0)
    (by decide +kernel) scS56Cut_caps_nonneg scS56Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS57CutCell) (roots := scS57CutRoots)
    (caps := scS57CutCaps) (weightFloor := scS57CutWeightFloor) (margins := scS57CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS57Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS57Cut_layer0)
    (by decide +kernel) scS57Cut_caps_nonneg scS57Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS58CutCell) (roots := scS58CutRoots)
    (caps := scS58CutCaps) (weightFloor := scS58CutWeightFloor) (margins := scS58CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS58Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS58Cut_layer0)
    (by decide +kernel) scS58Cut_caps_nonneg scS58Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS59CutCell) (roots := scS59CutRoots)
    (caps := scS59CutCaps) (weightFloor := scS59CutWeightFloor) (margins := scS59CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS59Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS59Cut_layer0)
    (by decide +kernel) scS59Cut_caps_nonneg scS59Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS60CutCell) (roots := scS60CutRoots)
    (caps := scS60CutCaps) (weightFloor := scS60CutWeightFloor) (margins := scS60CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS60Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS60Cut_layer0)
    (by decide +kernel) scS60Cut_caps_nonneg scS60Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS61CutCell) (roots := scS61CutRoots)
    (caps := scS61CutCaps) (weightFloor := scS61CutWeightFloor) (margins := scS61CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS61Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS61Cut_layer0)
    (by decide +kernel) scS61Cut_caps_nonneg scS61Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS62CutCell) (roots := scS62CutRoots)
    (caps := scS62CutCaps) (weightFloor := scS62CutWeightFloor) (margins := scS62CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS62Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS62Cut_layer0)
    (by decide +kernel) scS62Cut_caps_nonneg scS62Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS63CutCell) (roots := scS63CutRoots)
    (caps := scS63CutCaps) (weightFloor := scS63CutWeightFloor) (margins := scS63CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS63Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS63Cut_layer0)
    (by decide +kernel) scS63Cut_caps_nonneg scS63Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates064 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scS64CutCell) (roots := scS64CutRoots)
    (caps := scS64CutCaps) (weightFloor := scS64CutWeightFloor) (margins := scS64CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS64Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS64Cut_layer0)
    (by decide +kernel) scS64Cut_caps_nonneg scS64Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS65CutCell) (roots := scS65CutRoots)
    (caps := scS65CutCaps) (weightFloor := scS65CutWeightFloor) (margins := scS65CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS65Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS65Cut_layer0)
    (by decide +kernel) scS65Cut_caps_nonneg scS65Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS66CutCell) (roots := scS66CutRoots)
    (caps := scS66CutCaps) (weightFloor := scS66CutWeightFloor) (margins := scS66CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS66Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS66Cut_layer0)
    (by decide +kernel) scS66Cut_caps_nonneg scS66Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS67CutCell) (roots := scS67CutRoots)
    (caps := scS67CutCaps) (weightFloor := scS67CutWeightFloor) (margins := scS67CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS67Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS67Cut_layer0)
    (by decide +kernel) scS67Cut_caps_nonneg scS67Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS68CutCell) (roots := scS68CutRoots)
    (caps := scS68CutCaps) (weightFloor := scS68CutWeightFloor) (margins := scS68CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS68Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS68Cut_layer0)
    (by decide +kernel) scS68Cut_caps_nonneg scS68Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS69CutCell) (roots := scS69CutRoots)
    (caps := scS69CutCaps) (weightFloor := scS69CutWeightFloor) (margins := scS69CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS69Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS69Cut_layer0)
    (by decide +kernel) scS69Cut_caps_nonneg scS69Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS70CutCell) (roots := scS70CutRoots)
    (caps := scS70CutCaps) (weightFloor := scS70CutWeightFloor) (margins := scS70CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS70Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS70Cut_layer0)
    (by decide +kernel) scS70Cut_caps_nonneg scS70Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS71CutCell) (roots := scS71CutRoots)
    (caps := scS71CutCaps) (weightFloor := scS71CutWeightFloor) (margins := scS71CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS71Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS71Cut_layer0)
    (by decide +kernel) scS71Cut_caps_nonneg scS71Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS72CutCell) (roots := scS72CutRoots)
    (caps := scS72CutCaps) (weightFloor := scS72CutWeightFloor) (margins := scS72CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS72Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS72Cut_layer0)
    (by decide +kernel) scS72Cut_caps_nonneg scS72Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS73CutCell) (roots := scS73CutRoots)
    (caps := scS73CutCaps) (weightFloor := scS73CutWeightFloor) (margins := scS73CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS73Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS73Cut_layer0)
    (by decide +kernel) scS73Cut_caps_nonneg scS73Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS74CutCell) (roots := scS74CutRoots)
    (caps := scS74CutCaps) (weightFloor := scS74CutWeightFloor) (margins := scS74CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS74Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS74Cut_layer0)
    (by decide +kernel) scS74Cut_caps_nonneg scS74Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS75CutCell) (roots := scS75CutRoots)
    (caps := scS75CutCaps) (weightFloor := scS75CutWeightFloor) (margins := scS75CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS75Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS75Cut_layer0)
    (by decide +kernel) scS75Cut_caps_nonneg scS75Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS76CutCell) (roots := scS76CutRoots)
    (caps := scS76CutCaps) (weightFloor := scS76CutWeightFloor) (margins := scS76CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS76Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS76Cut_layer0)
    (by decide +kernel) scS76Cut_caps_nonneg scS76Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS77CutCell) (roots := scS77CutRoots)
    (caps := scS77CutCaps) (weightFloor := scS77CutWeightFloor) (margins := scS77CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS77Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS77Cut_layer0)
    (by decide +kernel) scS77Cut_caps_nonneg scS77Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS78CutCell) (roots := scS78CutRoots)
    (caps := scS78CutCaps) (weightFloor := scS78CutWeightFloor) (margins := scS78CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS78Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS78Cut_layer0)
    (by decide +kernel) scS78Cut_caps_nonneg scS78Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS79CutCell) (roots := scS79CutRoots)
    (caps := scS79CutCaps) (weightFloor := scS79CutWeightFloor) (margins := scS79CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS79Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS79Cut_layer0)
    (by decide +kernel) scS79Cut_caps_nonneg scS79Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS80CutCell) (roots := scS80CutRoots)
    (caps := scS80CutCaps) (weightFloor := scS80CutWeightFloor) (margins := scS80CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS80Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS80Cut_layer0)
    (by decide +kernel) scS80Cut_caps_nonneg scS80Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS81CutCell) (roots := scS81CutRoots)
    (caps := scS81CutCaps) (weightFloor := scS81CutWeightFloor) (margins := scS81CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS81Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS81Cut_layer0)
    (by decide +kernel) scS81Cut_caps_nonneg scS81Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS82CutCell) (roots := scS82CutRoots)
    (caps := scS82CutCaps) (weightFloor := scS82CutWeightFloor) (margins := scS82CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS82Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS82Cut_layer0)
    (by decide +kernel) scS82Cut_caps_nonneg scS82Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS83CutCell) (roots := scS83CutRoots)
    (caps := scS83CutCaps) (weightFloor := scS83CutWeightFloor) (margins := scS83CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS83Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS83Cut_layer0)
    (by decide +kernel) scS83Cut_caps_nonneg scS83Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS84CutCell) (roots := scS84CutRoots)
    (caps := scS84CutCaps) (weightFloor := scS84CutWeightFloor) (margins := scS84CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS84Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS84Cut_layer0)
    (by decide +kernel) scS84Cut_caps_nonneg scS84Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS85CutCell) (roots := scS85CutRoots)
    (caps := scS85CutCaps) (weightFloor := scS85CutWeightFloor) (margins := scS85CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS85Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS85Cut_layer0)
    (by decide +kernel) scS85Cut_caps_nonneg scS85Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS86CutCell) (roots := scS86CutRoots)
    (caps := scS86CutCaps) (weightFloor := scS86CutWeightFloor) (margins := scS86CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS86Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS86Cut_layer0)
    (by decide +kernel) scS86Cut_caps_nonneg scS86Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS87CutCell) (roots := scS87CutRoots)
    (caps := scS87CutCaps) (weightFloor := scS87CutWeightFloor) (margins := scS87CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS87Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS87Cut_layer0)
    (by decide +kernel) scS87Cut_caps_nonneg scS87Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS88CutCell) (roots := scS88CutRoots)
    (caps := scS88CutCaps) (weightFloor := scS88CutWeightFloor) (margins := scS88CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS88Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS88Cut_layer0)
    (by decide +kernel) scS88Cut_caps_nonneg scS88Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS89CutCell) (roots := scS89CutRoots)
    (caps := scS89CutCaps) (weightFloor := scS89CutWeightFloor) (margins := scS89CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS89Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS89Cut_layer0)
    (by decide +kernel) scS89Cut_caps_nonneg scS89Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS90CutCell) (roots := scS90CutRoots)
    (caps := scS90CutCaps) (weightFloor := scS90CutWeightFloor) (margins := scS90CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS90Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS90Cut_layer0)
    (by decide +kernel) scS90Cut_caps_nonneg scS90Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS91CutCell) (roots := scS91CutRoots)
    (caps := scS91CutCaps) (weightFloor := scS91CutWeightFloor) (margins := scS91CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS91Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS91Cut_layer0)
    (by decide +kernel) scS91Cut_caps_nonneg scS91Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS92CutCell) (roots := scS92CutRoots)
    (caps := scS92CutCaps) (weightFloor := scS92CutWeightFloor) (margins := scS92CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS92Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS92Cut_layer0)
    (by decide +kernel) scS92Cut_caps_nonneg scS92Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS93CutCell) (roots := scS93CutRoots)
    (caps := scS93CutCaps) (weightFloor := scS93CutWeightFloor) (margins := scS93CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS93Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS93Cut_layer0)
    (by decide +kernel) scS93Cut_caps_nonneg scS93Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS94CutCell) (roots := scS94CutRoots)
    (caps := scS94CutCaps) (weightFloor := scS94CutWeightFloor) (margins := scS94CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS94Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS94Cut_layer0)
    (by decide +kernel) scS94Cut_caps_nonneg scS94Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS95CutCell) (roots := scS95CutRoots)
    (caps := scS95CutCaps) (weightFloor := scS95CutWeightFloor) (margins := scS95CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS95Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS95Cut_layer0)
    (by decide +kernel) scS95Cut_caps_nonneg scS95Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates096 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scS96CutCell) (roots := scS96CutRoots)
    (caps := scS96CutCaps) (weightFloor := scS96CutWeightFloor) (margins := scS96CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS96Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS96Cut_layer0)
    (by decide +kernel) scS96Cut_caps_nonneg scS96Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS97CutCell) (roots := scS97CutRoots)
    (caps := scS97CutCaps) (weightFloor := scS97CutWeightFloor) (margins := scS97CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS97Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS97Cut_layer0)
    (by decide +kernel) scS97Cut_caps_nonneg scS97Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS98CutCell) (roots := scS98CutRoots)
    (caps := scS98CutCaps) (weightFloor := scS98CutWeightFloor) (margins := scS98CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS98Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS98Cut_layer0)
    (by decide +kernel) scS98Cut_caps_nonneg scS98Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS99CutCell) (roots := scS99CutRoots)
    (caps := scS99CutCaps) (weightFloor := scS99CutWeightFloor) (margins := scS99CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS99Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS99Cut_layer0)
    (by decide +kernel) scS99Cut_caps_nonneg scS99Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS100CutCell) (roots := scS100CutRoots)
    (caps := scS100CutCaps) (weightFloor := scS100CutWeightFloor) (margins := scS100CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS100Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS100Cut_layer0)
    (by decide +kernel) scS100Cut_caps_nonneg scS100Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS101CutCell) (roots := scS101CutRoots)
    (caps := scS101CutCaps) (weightFloor := scS101CutWeightFloor) (margins := scS101CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS101Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS101Cut_layer0)
    (by decide +kernel) scS101Cut_caps_nonneg scS101Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS102CutCell) (roots := scS102CutRoots)
    (caps := scS102CutCaps) (weightFloor := scS102CutWeightFloor) (margins := scS102CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS102Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS102Cut_layer0)
    (by decide +kernel) scS102Cut_caps_nonneg scS102Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS103CutCell) (roots := scS103CutRoots)
    (caps := scS103CutCaps) (weightFloor := scS103CutWeightFloor) (margins := scS103CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS103Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS103Cut_layer0)
    (by decide +kernel) scS103Cut_caps_nonneg scS103Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS104CutCell) (roots := scS104CutRoots)
    (caps := scS104CutCaps) (weightFloor := scS104CutWeightFloor) (margins := scS104CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS104Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS104Cut_layer0)
    (by decide +kernel) scS104Cut_caps_nonneg scS104Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS105CutCell) (roots := scS105CutRoots)
    (caps := scS105CutCaps) (weightFloor := scS105CutWeightFloor) (margins := scS105CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS105Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS105Cut_layer0)
    (by decide +kernel) scS105Cut_caps_nonneg scS105Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS106CutCell) (roots := scS106CutRoots)
    (caps := scS106CutCaps) (weightFloor := scS106CutWeightFloor) (margins := scS106CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS106Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS106Cut_layer0)
    (by decide +kernel) scS106Cut_caps_nonneg scS106Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS107CutCell) (roots := scS107CutRoots)
    (caps := scS107CutCaps) (weightFloor := scS107CutWeightFloor) (margins := scS107CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS107Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS107Cut_layer0)
    (by decide +kernel) scS107Cut_caps_nonneg scS107Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS108CutCell) (roots := scS108CutRoots)
    (caps := scS108CutCaps) (weightFloor := scS108CutWeightFloor) (margins := scS108CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS108Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS108Cut_layer0)
    (by decide +kernel) scS108Cut_caps_nonneg scS108Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS109CutCell) (roots := scS109CutRoots)
    (caps := scS109CutCaps) (weightFloor := scS109CutWeightFloor) (margins := scS109CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS109Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS109Cut_layer0)
    (by decide +kernel) scS109Cut_caps_nonneg scS109Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS110CutCell) (roots := scS110CutRoots)
    (caps := scS110CutCaps) (weightFloor := scS110CutWeightFloor) (margins := scS110CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS110Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS110Cut_layer0)
    (by decide +kernel) scS110Cut_caps_nonneg scS110Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS111CutCell) (roots := scS111CutRoots)
    (caps := scS111CutCaps) (weightFloor := scS111CutWeightFloor) (margins := scS111CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS111Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS111Cut_layer0)
    (by decide +kernel) scS111Cut_caps_nonneg scS111Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS112CutCell) (roots := scS112CutRoots)
    (caps := scS112CutCaps) (weightFloor := scS112CutWeightFloor) (margins := scS112CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS112Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS112Cut_layer0)
    (by decide +kernel) scS112Cut_caps_nonneg scS112Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS113CutCell) (roots := scS113CutRoots)
    (caps := scS113CutCaps) (weightFloor := scS113CutWeightFloor) (margins := scS113CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS113Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS113Cut_layer0)
    (by decide +kernel) scS113Cut_caps_nonneg scS113Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS114CutCell) (roots := scS114CutRoots)
    (caps := scS114CutCaps) (weightFloor := scS114CutWeightFloor) (margins := scS114CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS114Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS114Cut_layer0)
    (by decide +kernel) scS114Cut_caps_nonneg scS114Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS115CutCell) (roots := scS115CutRoots)
    (caps := scS115CutCaps) (weightFloor := scS115CutWeightFloor) (margins := scS115CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS115Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS115Cut_layer0)
    (by decide +kernel) scS115Cut_caps_nonneg scS115Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS116CutCell) (roots := scS116CutRoots)
    (caps := scS116CutCaps) (weightFloor := scS116CutWeightFloor) (margins := scS116CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS116Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS116Cut_layer0)
    (by decide +kernel) scS116Cut_caps_nonneg scS116Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS117CutCell) (roots := scS117CutRoots)
    (caps := scS117CutCaps) (weightFloor := scS117CutWeightFloor) (margins := scS117CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS117Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS117Cut_layer0)
    (by decide +kernel) scS117Cut_caps_nonneg scS117Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS118CutCell) (roots := scS118CutRoots)
    (caps := scS118CutCaps) (weightFloor := scS118CutWeightFloor) (margins := scS118CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS118Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS118Cut_layer0)
    (by decide +kernel) scS118Cut_caps_nonneg scS118Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS119CutCell) (roots := scS119CutRoots)
    (caps := scS119CutCaps) (weightFloor := scS119CutWeightFloor) (margins := scS119CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS119Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS119Cut_layer0)
    (by decide +kernel) scS119Cut_caps_nonneg scS119Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS120CutCell) (roots := scS120CutRoots)
    (caps := scS120CutCaps) (weightFloor := scS120CutWeightFloor) (margins := scS120CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS120Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS120Cut_layer0)
    (by decide +kernel) scS120Cut_caps_nonneg scS120Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS121CutCell) (roots := scS121CutRoots)
    (caps := scS121CutCaps) (weightFloor := scS121CutWeightFloor) (margins := scS121CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS121Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS121Cut_layer0)
    (by decide +kernel) scS121Cut_caps_nonneg scS121Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS122CutCell) (roots := scS122CutRoots)
    (caps := scS122CutCaps) (weightFloor := scS122CutWeightFloor) (margins := scS122CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS122Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS122Cut_layer0)
    (by decide +kernel) scS122Cut_caps_nonneg scS122Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS123CutCell) (roots := scS123CutRoots)
    (caps := scS123CutCaps) (weightFloor := scS123CutWeightFloor) (margins := scS123CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS123Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS123Cut_layer0)
    (by decide +kernel) scS123Cut_caps_nonneg scS123Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS124CutCell) (roots := scS124CutRoots)
    (caps := scS124CutCaps) (weightFloor := scS124CutWeightFloor) (margins := scS124CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS124Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS124Cut_layer0)
    (by decide +kernel) scS124Cut_caps_nonneg scS124Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS125CutCell) (roots := scS125CutRoots)
    (caps := scS125CutCaps) (weightFloor := scS125CutWeightFloor) (margins := scS125CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS125Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS125Cut_layer0)
    (by decide +kernel) scS125Cut_caps_nonneg scS125Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS126CutCell) (roots := scS126CutRoots)
    (caps := scS126CutCaps) (weightFloor := scS126CutWeightFloor) (margins := scS126CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS126Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS126Cut_layer0)
    (by decide +kernel) scS126Cut_caps_nonneg scS126Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS127CutCell) (roots := scS127CutRoots)
    (caps := scS127CutCaps) (weightFloor := scS127CutWeightFloor) (margins := scS127CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS127Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS127Cut_layer0)
    (by decide +kernel) scS127Cut_caps_nonneg scS127Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates128 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scS128CutCell) (roots := scS128CutRoots)
    (caps := scS128CutCaps) (weightFloor := scS128CutWeightFloor) (margins := scS128CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS128Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS128Cut_layer0)
    (by decide +kernel) scS128Cut_caps_nonneg scS128Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS129CutCell) (roots := scS129CutRoots)
    (caps := scS129CutCaps) (weightFloor := scS129CutWeightFloor) (margins := scS129CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS129Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS129Cut_layer0)
    (by decide +kernel) scS129Cut_caps_nonneg scS129Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS130CutCell) (roots := scS130CutRoots)
    (caps := scS130CutCaps) (weightFloor := scS130CutWeightFloor) (margins := scS130CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS130Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS130Cut_layer0)
    (by decide +kernel) scS130Cut_caps_nonneg scS130Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS131CutCell) (roots := scS131CutRoots)
    (caps := scS131CutCaps) (weightFloor := scS131CutWeightFloor) (margins := scS131CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS131Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS131Cut_layer0)
    (by decide +kernel) scS131Cut_caps_nonneg scS131Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS132CutCell) (roots := scS132CutRoots)
    (caps := scS132CutCaps) (weightFloor := scS132CutWeightFloor) (margins := scS132CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS132Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS132Cut_layer0)
    (by decide +kernel) scS132Cut_caps_nonneg scS132Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS133CutCell) (roots := scS133CutRoots)
    (caps := scS133CutCaps) (weightFloor := scS133CutWeightFloor) (margins := scS133CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS133Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS133Cut_layer0)
    (by decide +kernel) scS133Cut_caps_nonneg scS133Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS134CutCell) (roots := scS134CutRoots)
    (caps := scS134CutCaps) (weightFloor := scS134CutWeightFloor) (margins := scS134CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS134Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS134Cut_layer0)
    (by decide +kernel) scS134Cut_caps_nonneg scS134Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS135CutCell) (roots := scS135CutRoots)
    (caps := scS135CutCaps) (weightFloor := scS135CutWeightFloor) (margins := scS135CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS135Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS135Cut_layer0)
    (by decide +kernel) scS135Cut_caps_nonneg scS135Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS136CutCell) (roots := scS136CutRoots)
    (caps := scS136CutCaps) (weightFloor := scS136CutWeightFloor) (margins := scS136CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS136Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS136Cut_layer0)
    (by decide +kernel) scS136Cut_caps_nonneg scS136Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS137CutCell) (roots := scS137CutRoots)
    (caps := scS137CutCaps) (weightFloor := scS137CutWeightFloor) (margins := scS137CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS137Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS137Cut_layer0)
    (by decide +kernel) scS137Cut_caps_nonneg scS137Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS138CutCell) (roots := scS138CutRoots)
    (caps := scS138CutCaps) (weightFloor := scS138CutWeightFloor) (margins := scS138CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS138Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS138Cut_layer0)
    (by decide +kernel) scS138Cut_caps_nonneg scS138Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS139CutCell) (roots := scS139CutRoots)
    (caps := scS139CutCaps) (weightFloor := scS139CutWeightFloor) (margins := scS139CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS139Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS139Cut_layer0)
    (by decide +kernel) scS139Cut_caps_nonneg scS139Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS140CutCell) (roots := scS140CutRoots)
    (caps := scS140CutCaps) (weightFloor := scS140CutWeightFloor) (margins := scS140CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS140Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS140Cut_layer0)
    (by decide +kernel) scS140Cut_caps_nonneg scS140Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS141CutCell) (roots := scS141CutRoots)
    (caps := scS141CutCaps) (weightFloor := scS141CutWeightFloor) (margins := scS141CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS141Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS141Cut_layer0)
    (by decide +kernel) scS141Cut_caps_nonneg scS141Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS142CutCell) (roots := scS142CutRoots)
    (caps := scS142CutCaps) (weightFloor := scS142CutWeightFloor) (margins := scS142CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS142Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS142Cut_layer0)
    (by decide +kernel) scS142Cut_caps_nonneg scS142Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS143CutCell) (roots := scS143CutRoots)
    (caps := scS143CutCaps) (weightFloor := scS143CutWeightFloor) (margins := scS143CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS143Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS143Cut_layer0)
    (by decide +kernel) scS143Cut_caps_nonneg scS143Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS144CutCell) (roots := scS144CutRoots)
    (caps := scS144CutCaps) (weightFloor := scS144CutWeightFloor) (margins := scS144CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS144Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS144Cut_layer0)
    (by decide +kernel) scS144Cut_caps_nonneg scS144Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS145CutCell) (roots := scS145CutRoots)
    (caps := scS145CutCaps) (weightFloor := scS145CutWeightFloor) (margins := scS145CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS145Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS145Cut_layer0)
    (by decide +kernel) scS145Cut_caps_nonneg scS145Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS146CutCell) (roots := scS146CutRoots)
    (caps := scS146CutCaps) (weightFloor := scS146CutWeightFloor) (margins := scS146CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS146Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS146Cut_layer0)
    (by decide +kernel) scS146Cut_caps_nonneg scS146Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS147CutCell) (roots := scS147CutRoots)
    (caps := scS147CutCaps) (weightFloor := scS147CutWeightFloor) (margins := scS147CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS147Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS147Cut_layer0)
    (by decide +kernel) scS147Cut_caps_nonneg scS147Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS148CutCell) (roots := scS148CutRoots)
    (caps := scS148CutCaps) (weightFloor := scS148CutWeightFloor) (margins := scS148CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS148Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS148Cut_layer0)
    (by decide +kernel) scS148Cut_caps_nonneg scS148Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS149CutCell) (roots := scS149CutRoots)
    (caps := scS149CutCaps) (weightFloor := scS149CutWeightFloor) (margins := scS149CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS149Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS149Cut_layer0)
    (by decide +kernel) scS149Cut_caps_nonneg scS149Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS150CutCell) (roots := scS150CutRoots)
    (caps := scS150CutCaps) (weightFloor := scS150CutWeightFloor) (margins := scS150CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS150Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS150Cut_layer0)
    (by decide +kernel) scS150Cut_caps_nonneg scS150Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS151CutCell) (roots := scS151CutRoots)
    (caps := scS151CutCaps) (weightFloor := scS151CutWeightFloor) (margins := scS151CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS151Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS151Cut_layer0)
    (by decide +kernel) scS151Cut_caps_nonneg scS151Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS152CutCell) (roots := scS152CutRoots)
    (caps := scS152CutCaps) (weightFloor := scS152CutWeightFloor) (margins := scS152CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS152Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS152Cut_layer0)
    (by decide +kernel) scS152Cut_caps_nonneg scS152Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS153CutCell) (roots := scS153CutRoots)
    (caps := scS153CutCaps) (weightFloor := scS153CutWeightFloor) (margins := scS153CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS153Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS153Cut_layer0)
    (by decide +kernel) scS153Cut_caps_nonneg scS153Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS154CutCell) (roots := scS154CutRoots)
    (caps := scS154CutCaps) (weightFloor := scS154CutWeightFloor) (margins := scS154CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS154Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS154Cut_layer0)
    (by decide +kernel) scS154Cut_caps_nonneg scS154Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS155CutCell) (roots := scS155CutRoots)
    (caps := scS155CutCaps) (weightFloor := scS155CutWeightFloor) (margins := scS155CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS155Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS155Cut_layer0)
    (by decide +kernel) scS155Cut_caps_nonneg scS155Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS156CutCell) (roots := scS156CutRoots)
    (caps := scS156CutCaps) (weightFloor := scS156CutWeightFloor) (margins := scS156CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS156Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS156Cut_layer0)
    (by decide +kernel) scS156Cut_caps_nonneg scS156Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS157CutCell) (roots := scS157CutRoots)
    (caps := scS157CutCaps) (weightFloor := scS157CutWeightFloor) (margins := scS157CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS157Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS157Cut_layer0)
    (by decide +kernel) scS157Cut_caps_nonneg scS157Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS158CutCell) (roots := scS158CutRoots)
    (caps := scS158CutCaps) (weightFloor := scS158CutWeightFloor) (margins := scS158CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS158Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS158Cut_layer0)
    (by decide +kernel) scS158Cut_caps_nonneg scS158Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS159CutCell) (roots := scS159CutRoots)
    (caps := scS159CutCaps) (weightFloor := scS159CutWeightFloor) (margins := scS159CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS159Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS159Cut_layer0)
    (by decide +kernel) scS159Cut_caps_nonneg scS159Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates160 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scS160CutCell) (roots := scS160CutRoots)
    (caps := scS160CutCaps) (weightFloor := scS160CutWeightFloor) (margins := scS160CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS160Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS160Cut_layer0)
    (by decide +kernel) scS160Cut_caps_nonneg scS160Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS161CutCell) (roots := scS161CutRoots)
    (caps := scS161CutCaps) (weightFloor := scS161CutWeightFloor) (margins := scS161CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS161Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS161Cut_layer0)
    (by decide +kernel) scS161Cut_caps_nonneg scS161Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS162CutCell) (roots := scS162CutRoots)
    (caps := scS162CutCaps) (weightFloor := scS162CutWeightFloor) (margins := scS162CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS162Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS162Cut_layer0)
    (by decide +kernel) scS162Cut_caps_nonneg scS162Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS163CutCell) (roots := scS163CutRoots)
    (caps := scS163CutCaps) (weightFloor := scS163CutWeightFloor) (margins := scS163CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS163Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS163Cut_layer0)
    (by decide +kernel) scS163Cut_caps_nonneg scS163Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS164CutCell) (roots := scS164CutRoots)
    (caps := scS164CutCaps) (weightFloor := scS164CutWeightFloor) (margins := scS164CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS164Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS164Cut_layer0)
    (by decide +kernel) scS164Cut_caps_nonneg scS164Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS165CutCell) (roots := scS165CutRoots)
    (caps := scS165CutCaps) (weightFloor := scS165CutWeightFloor) (margins := scS165CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS165Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS165Cut_layer0)
    (by decide +kernel) scS165Cut_caps_nonneg scS165Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS166CutCell) (roots := scS166CutRoots)
    (caps := scS166CutCaps) (weightFloor := scS166CutWeightFloor) (margins := scS166CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS166Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS166Cut_layer0)
    (by decide +kernel) scS166Cut_caps_nonneg scS166Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS167CutCell) (roots := scS167CutRoots)
    (caps := scS167CutCaps) (weightFloor := scS167CutWeightFloor) (margins := scS167CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS167Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS167Cut_layer0)
    (by decide +kernel) scS167Cut_caps_nonneg scS167Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS168CutCell) (roots := scS168CutRoots)
    (caps := scS168CutCaps) (weightFloor := scS168CutWeightFloor) (margins := scS168CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS168Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS168Cut_layer0)
    (by decide +kernel) scS168Cut_caps_nonneg scS168Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS169CutCell) (roots := scS169CutRoots)
    (caps := scS169CutCaps) (weightFloor := scS169CutWeightFloor) (margins := scS169CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS169Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS169Cut_layer0)
    (by decide +kernel) scS169Cut_caps_nonneg scS169Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS170CutCell) (roots := scS170CutRoots)
    (caps := scS170CutCaps) (weightFloor := scS170CutWeightFloor) (margins := scS170CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS170Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS170Cut_layer0)
    (by decide +kernel) scS170Cut_caps_nonneg scS170Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS171CutCell) (roots := scS171CutRoots)
    (caps := scS171CutCaps) (weightFloor := scS171CutWeightFloor) (margins := scS171CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS171Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS171Cut_layer0)
    (by decide +kernel) scS171Cut_caps_nonneg scS171Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS172CutCell) (roots := scS172CutRoots)
    (caps := scS172CutCaps) (weightFloor := scS172CutWeightFloor) (margins := scS172CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS172Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS172Cut_layer0)
    (by decide +kernel) scS172Cut_caps_nonneg scS172Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS173CutCell) (roots := scS173CutRoots)
    (caps := scS173CutCaps) (weightFloor := scS173CutWeightFloor) (margins := scS173CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS173Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS173Cut_layer0)
    (by decide +kernel) scS173Cut_caps_nonneg scS173Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS174CutCell) (roots := scS174CutRoots)
    (caps := scS174CutCaps) (weightFloor := scS174CutWeightFloor) (margins := scS174CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS174Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS174Cut_layer0)
    (by decide +kernel) scS174Cut_caps_nonneg scS174Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS175CutCell) (roots := scS175CutRoots)
    (caps := scS175CutCaps) (weightFloor := scS175CutWeightFloor) (margins := scS175CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS175Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS175Cut_layer0)
    (by decide +kernel) scS175Cut_caps_nonneg scS175Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS176CutCell) (roots := scS176CutRoots)
    (caps := scS176CutCaps) (weightFloor := scS176CutWeightFloor) (margins := scS176CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS176Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS176Cut_layer0)
    (by decide +kernel) scS176Cut_caps_nonneg scS176Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS177CutCell) (roots := scS177CutRoots)
    (caps := scS177CutCaps) (weightFloor := scS177CutWeightFloor) (margins := scS177CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS177Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS177Cut_layer0)
    (by decide +kernel) scS177Cut_caps_nonneg scS177Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS178CutCell) (roots := scS178CutRoots)
    (caps := scS178CutCaps) (weightFloor := scS178CutWeightFloor) (margins := scS178CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS178Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS178Cut_layer0)
    (by decide +kernel) scS178Cut_caps_nonneg scS178Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS179CutCell) (roots := scS179CutRoots)
    (caps := scS179CutCaps) (weightFloor := scS179CutWeightFloor) (margins := scS179CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS179Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS179Cut_layer0)
    (by decide +kernel) scS179Cut_caps_nonneg scS179Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS180CutCell) (roots := scS180CutRoots)
    (caps := scS180CutCaps) (weightFloor := scS180CutWeightFloor) (margins := scS180CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS180Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS180Cut_layer0)
    (by decide +kernel) scS180Cut_caps_nonneg scS180Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS181CutCell) (roots := scS181CutRoots)
    (caps := scS181CutCaps) (weightFloor := scS181CutWeightFloor) (margins := scS181CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS181Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS181Cut_layer0)
    (by decide +kernel) scS181Cut_caps_nonneg scS181Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS182CutCell) (roots := scS182CutRoots)
    (caps := scS182CutCaps) (weightFloor := scS182CutWeightFloor) (margins := scS182CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS182Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS182Cut_layer0)
    (by decide +kernel) scS182Cut_caps_nonneg scS182Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS183CutCell) (roots := scS183CutRoots)
    (caps := scS183CutCaps) (weightFloor := scS183CutWeightFloor) (margins := scS183CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS183Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS183Cut_layer0)
    (by decide +kernel) scS183Cut_caps_nonneg scS183Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS184CutCell) (roots := scS184CutRoots)
    (caps := scS184CutCaps) (weightFloor := scS184CutWeightFloor) (margins := scS184CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS184Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS184Cut_layer0)
    (by decide +kernel) scS184Cut_caps_nonneg scS184Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS185CutCell) (roots := scS185CutRoots)
    (caps := scS185CutCaps) (weightFloor := scS185CutWeightFloor) (margins := scS185CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS185Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS185Cut_layer0)
    (by decide +kernel) scS185Cut_caps_nonneg scS185Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS186CutCell) (roots := scS186CutRoots)
    (caps := scS186CutCaps) (weightFloor := scS186CutWeightFloor) (margins := scS186CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS186Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS186Cut_layer0)
    (by decide +kernel) scS186Cut_caps_nonneg scS186Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS187CutCell) (roots := scS187CutRoots)
    (caps := scS187CutCaps) (weightFloor := scS187CutWeightFloor) (margins := scS187CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS187Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS187Cut_layer0)
    (by decide +kernel) scS187Cut_caps_nonneg scS187Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS188CutCell) (roots := scS188CutRoots)
    (caps := scS188CutCaps) (weightFloor := scS188CutWeightFloor) (margins := scS188CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS188Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS188Cut_layer0)
    (by decide +kernel) scS188Cut_caps_nonneg scS188Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS189CutCell) (roots := scS189CutRoots)
    (caps := scS189CutCaps) (weightFloor := scS189CutWeightFloor) (margins := scS189CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS189Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS189Cut_layer0)
    (by decide +kernel) scS189Cut_caps_nonneg scS189Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS190CutCell) (roots := scS190CutRoots)
    (caps := scS190CutCaps) (weightFloor := scS190CutWeightFloor) (margins := scS190CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS190Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS190Cut_layer0)
    (by decide +kernel) scS190Cut_caps_nonneg scS190Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS191CutCell) (roots := scS191CutRoots)
    (caps := scS191CutCaps) (weightFloor := scS191CutWeightFloor) (margins := scS191CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS191Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS191Cut_layer0)
    (by decide +kernel) scS191Cut_caps_nonneg scS191Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates192 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scS192CutCell) (roots := scS192CutRoots)
    (caps := scS192CutCaps) (weightFloor := scS192CutWeightFloor) (margins := scS192CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS192Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS192Cut_layer0)
    (by decide +kernel) scS192Cut_caps_nonneg scS192Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS193CutCell) (roots := scS193CutRoots)
    (caps := scS193CutCaps) (weightFloor := scS193CutWeightFloor) (margins := scS193CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS193Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS193Cut_layer0)
    (by decide +kernel) scS193Cut_caps_nonneg scS193Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS194CutCell) (roots := scS194CutRoots)
    (caps := scS194CutCaps) (weightFloor := scS194CutWeightFloor) (margins := scS194CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS194Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS194Cut_layer0)
    (by decide +kernel) scS194Cut_caps_nonneg scS194Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS195CutCell) (roots := scS195CutRoots)
    (caps := scS195CutCaps) (weightFloor := scS195CutWeightFloor) (margins := scS195CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS195Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS195Cut_layer0)
    (by decide +kernel) scS195Cut_caps_nonneg scS195Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS196CutCell) (roots := scS196CutRoots)
    (caps := scS196CutCaps) (weightFloor := scS196CutWeightFloor) (margins := scS196CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS196Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS196Cut_layer0)
    (by decide +kernel) scS196Cut_caps_nonneg scS196Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS197CutCell) (roots := scS197CutRoots)
    (caps := scS197CutCaps) (weightFloor := scS197CutWeightFloor) (margins := scS197CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS197Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS197Cut_layer0)
    (by decide +kernel) scS197Cut_caps_nonneg scS197Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS198CutCell) (roots := scS198CutRoots)
    (caps := scS198CutCaps) (weightFloor := scS198CutWeightFloor) (margins := scS198CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS198Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS198Cut_layer0)
    (by decide +kernel) scS198Cut_caps_nonneg scS198Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS199CutCell) (roots := scS199CutRoots)
    (caps := scS199CutCaps) (weightFloor := scS199CutWeightFloor) (margins := scS199CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS199Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS199Cut_layer0)
    (by decide +kernel) scS199Cut_caps_nonneg scS199Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS200CutCell) (roots := scS200CutRoots)
    (caps := scS200CutCaps) (weightFloor := scS200CutWeightFloor) (margins := scS200CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS200Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS200Cut_layer0)
    (by decide +kernel) scS200Cut_caps_nonneg scS200Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS201CutCell) (roots := scS201CutRoots)
    (caps := scS201CutCaps) (weightFloor := scS201CutWeightFloor) (margins := scS201CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS201Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS201Cut_layer0)
    (by decide +kernel) scS201Cut_caps_nonneg scS201Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS202CutCell) (roots := scS202CutRoots)
    (caps := scS202CutCaps) (weightFloor := scS202CutWeightFloor) (margins := scS202CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS202Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS202Cut_layer0)
    (by decide +kernel) scS202Cut_caps_nonneg scS202Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scS203CutCell) (roots := scS203CutRoots)
    (caps := scS203CutCaps) (weightFloor := scS203CutWeightFloor) (margins := scS203CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scS203Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scS203Cut_layer0)
    (by decide +kernel) scS203Cut_caps_nonneg scS203Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD0CutCell) (roots := scD0CutRoots)
    (caps := scD0CutCaps) (weightFloor := scD0CutWeightFloor) (margins := scD0CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD0Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD0Cut_layer0)
    (by decide +kernel) scD0Cut_caps_nonneg scD0Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD1CutCell) (roots := scD1CutRoots)
    (caps := scD1CutCaps) (weightFloor := scD1CutWeightFloor) (margins := scD1CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD1Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD1Cut_layer0)
    (by decide +kernel) scD1Cut_caps_nonneg scD1Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD2CutCell) (roots := scD2CutRoots)
    (caps := scD2CutCaps) (weightFloor := scD2CutWeightFloor) (margins := scD2CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD2Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD2Cut_layer0)
    (by decide +kernel) scD2Cut_caps_nonneg scD2Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD3CutCell) (roots := scD3CutRoots)
    (caps := scD3CutCaps) (weightFloor := scD3CutWeightFloor) (margins := scD3CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD3Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD3Cut_layer0)
    (by decide +kernel) scD3Cut_caps_nonneg scD3Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD4CutCell) (roots := scD4CutRoots)
    (caps := scD4CutCaps) (weightFloor := scD4CutWeightFloor) (margins := scD4CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD4Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD4Cut_layer0)
    (by decide +kernel) scD4Cut_caps_nonneg scD4Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD5CutCell) (roots := scD5CutRoots)
    (caps := scD5CutCaps) (weightFloor := scD5CutWeightFloor) (margins := scD5CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD5Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD5Cut_layer0)
    (by decide +kernel) scD5Cut_caps_nonneg scD5Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD6CutCell) (roots := scD6CutRoots)
    (caps := scD6CutCaps) (weightFloor := scD6CutWeightFloor) (margins := scD6CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD6Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD6Cut_layer0)
    (by decide +kernel) scD6Cut_caps_nonneg scD6Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD7CutCell) (roots := scD7CutRoots)
    (caps := scD7CutCaps) (weightFloor := scD7CutWeightFloor) (margins := scD7CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD7Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD7Cut_layer0)
    (by decide +kernel) scD7Cut_caps_nonneg scD7Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD8CutCell) (roots := scD8CutRoots)
    (caps := scD8CutCaps) (weightFloor := scD8CutWeightFloor) (margins := scD8CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD8Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD8Cut_layer0)
    (by decide +kernel) scD8Cut_caps_nonneg scD8Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD9CutCell) (roots := scD9CutRoots)
    (caps := scD9CutCaps) (weightFloor := scD9CutWeightFloor) (margins := scD9CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD9Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD9Cut_layer0)
    (by decide +kernel) scD9Cut_caps_nonneg scD9Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD10CutCell) (roots := scD10CutRoots)
    (caps := scD10CutCaps) (weightFloor := scD10CutWeightFloor) (margins := scD10CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD10Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD10Cut_layer0)
    (by decide +kernel) scD10Cut_caps_nonneg scD10Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD11CutCell) (roots := scD11CutRoots)
    (caps := scD11CutCaps) (weightFloor := scD11CutWeightFloor) (margins := scD11CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD11Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD11Cut_layer0)
    (by decide +kernel) scD11Cut_caps_nonneg scD11Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD12CutCell) (roots := scD12CutRoots)
    (caps := scD12CutCaps) (weightFloor := scD12CutWeightFloor) (margins := scD12CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD12Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD12Cut_layer0)
    (by decide +kernel) scD12Cut_caps_nonneg scD12Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD13CutCell) (roots := scD13CutRoots)
    (caps := scD13CutCaps) (weightFloor := scD13CutWeightFloor) (margins := scD13CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD13Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD13Cut_layer0)
    (by decide +kernel) scD13Cut_caps_nonneg scD13Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD14CutCell) (roots := scD14CutRoots)
    (caps := scD14CutCaps) (weightFloor := scD14CutWeightFloor) (margins := scD14CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD14Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD14Cut_layer0)
    (by decide +kernel) scD14Cut_caps_nonneg scD14Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD15CutCell) (roots := scD15CutRoots)
    (caps := scD15CutCaps) (weightFloor := scD15CutWeightFloor) (margins := scD15CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD15Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD15Cut_layer0)
    (by decide +kernel) scD15Cut_caps_nonneg scD15Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD16CutCell) (roots := scD16CutRoots)
    (caps := scD16CutCaps) (weightFloor := scD16CutWeightFloor) (margins := scD16CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD16Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD16Cut_layer0)
    (by decide +kernel) scD16Cut_caps_nonneg scD16Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD17CutCell) (roots := scD17CutRoots)
    (caps := scD17CutCaps) (weightFloor := scD17CutWeightFloor) (margins := scD17CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD17Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD17Cut_layer0)
    (by decide +kernel) scD17Cut_caps_nonneg scD17Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD18CutCell) (roots := scD18CutRoots)
    (caps := scD18CutCaps) (weightFloor := scD18CutWeightFloor) (margins := scD18CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD18Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD18Cut_layer0)
    (by decide +kernel) scD18Cut_caps_nonneg scD18Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD19CutCell) (roots := scD19CutRoots)
    (caps := scD19CutCaps) (weightFloor := scD19CutWeightFloor) (margins := scD19CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD19Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD19Cut_layer0)
    (by decide +kernel) scD19Cut_caps_nonneg scD19Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates224 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scD20CutCell) (roots := scD20CutRoots)
    (caps := scD20CutCaps) (weightFloor := scD20CutWeightFloor) (margins := scD20CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD20Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD20Cut_layer0)
    (by decide +kernel) scD20Cut_caps_nonneg scD20Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD21CutCell) (roots := scD21CutRoots)
    (caps := scD21CutCaps) (weightFloor := scD21CutWeightFloor) (margins := scD21CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD21Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD21Cut_layer0)
    (by decide +kernel) scD21Cut_caps_nonneg scD21Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD22CutCell) (roots := scD22CutRoots)
    (caps := scD22CutCaps) (weightFloor := scD22CutWeightFloor) (margins := scD22CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD22Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD22Cut_layer0)
    (by decide +kernel) scD22Cut_caps_nonneg scD22Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD23CutCell) (roots := scD23CutRoots)
    (caps := scD23CutCaps) (weightFloor := scD23CutWeightFloor) (margins := scD23CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD23Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD23Cut_layer0)
    (by decide +kernel) scD23Cut_caps_nonneg scD23Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD24CutCell) (roots := scD24CutRoots)
    (caps := scD24CutCaps) (weightFloor := scD24CutWeightFloor) (margins := scD24CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD24Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD24Cut_layer0)
    (by decide +kernel) scD24Cut_caps_nonneg scD24Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD25CutCell) (roots := scD25CutRoots)
    (caps := scD25CutCaps) (weightFloor := scD25CutWeightFloor) (margins := scD25CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD25Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD25Cut_layer0)
    (by decide +kernel) scD25Cut_caps_nonneg scD25Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD26CutCell) (roots := scD26CutRoots)
    (caps := scD26CutCaps) (weightFloor := scD26CutWeightFloor) (margins := scD26CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD26Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD26Cut_layer0)
    (by decide +kernel) scD26Cut_caps_nonneg scD26Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD27CutCell) (roots := scD27CutRoots)
    (caps := scD27CutCaps) (weightFloor := scD27CutWeightFloor) (margins := scD27CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD27Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD27Cut_layer0)
    (by decide +kernel) scD27Cut_caps_nonneg scD27Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD28CutCell) (roots := scD28CutRoots)
    (caps := scD28CutCaps) (weightFloor := scD28CutWeightFloor) (margins := scD28CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD28Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD28Cut_layer0)
    (by decide +kernel) scD28Cut_caps_nonneg scD28Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD29CutCell) (roots := scD29CutRoots)
    (caps := scD29CutCaps) (weightFloor := scD29CutWeightFloor) (margins := scD29CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD29Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD29Cut_layer0)
    (by decide +kernel) scD29Cut_caps_nonneg scD29Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD30CutCell) (roots := scD30CutRoots)
    (caps := scD30CutCaps) (weightFloor := scD30CutWeightFloor) (margins := scD30CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD30Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD30Cut_layer0)
    (by decide +kernel) scD30Cut_caps_nonneg scD30Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD31CutCell) (roots := scD31CutRoots)
    (caps := scD31CutCaps) (weightFloor := scD31CutWeightFloor) (margins := scD31CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD31Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD31Cut_layer0)
    (by decide +kernel) scD31Cut_caps_nonneg scD31Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD32CutCell) (roots := scD32CutRoots)
    (caps := scD32CutCaps) (weightFloor := scD32CutWeightFloor) (margins := scD32CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD32Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD32Cut_layer0)
    (by decide +kernel) scD32Cut_caps_nonneg scD32Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD33CutCell) (roots := scD33CutRoots)
    (caps := scD33CutCaps) (weightFloor := scD33CutWeightFloor) (margins := scD33CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD33Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD33Cut_layer0)
    (by decide +kernel) scD33Cut_caps_nonneg scD33Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD34CutCell) (roots := scD34CutRoots)
    (caps := scD34CutCaps) (weightFloor := scD34CutWeightFloor) (margins := scD34CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD34Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD34Cut_layer0)
    (by decide +kernel) scD34Cut_caps_nonneg scD34Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD35CutCell) (roots := scD35CutRoots)
    (caps := scD35CutCaps) (weightFloor := scD35CutWeightFloor) (margins := scD35CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD35Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD35Cut_layer0)
    (by decide +kernel) scD35Cut_caps_nonneg scD35Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD36CutCell) (roots := scD36CutRoots)
    (caps := scD36CutCaps) (weightFloor := scD36CutWeightFloor) (margins := scD36CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD36Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD36Cut_layer0)
    (by decide +kernel) scD36Cut_caps_nonneg scD36Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD37CutCell) (roots := scD37CutRoots)
    (caps := scD37CutCaps) (weightFloor := scD37CutWeightFloor) (margins := scD37CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD37Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD37Cut_layer0)
    (by decide +kernel) scD37Cut_caps_nonneg scD37Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD38CutCell) (roots := scD38CutRoots)
    (caps := scD38CutCaps) (weightFloor := scD38CutWeightFloor) (margins := scD38CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD38Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD38Cut_layer0)
    (by decide +kernel) scD38Cut_caps_nonneg scD38Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD39CutCell) (roots := scD39CutRoots)
    (caps := scD39CutCaps) (weightFloor := scD39CutWeightFloor) (margins := scD39CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD39Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD39Cut_layer0)
    (by decide +kernel) scD39Cut_caps_nonneg scD39Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD40CutCell) (roots := scD40CutRoots)
    (caps := scD40CutCaps) (weightFloor := scD40CutWeightFloor) (margins := scD40CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD40Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD40Cut_layer0)
    (by decide +kernel) scD40Cut_caps_nonneg scD40Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD41CutCell) (roots := scD41CutRoots)
    (caps := scD41CutCaps) (weightFloor := scD41CutWeightFloor) (margins := scD41CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD41Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD41Cut_layer0)
    (by decide +kernel) scD41Cut_caps_nonneg scD41Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD42CutCell) (roots := scD42CutRoots)
    (caps := scD42CutCaps) (weightFloor := scD42CutWeightFloor) (margins := scD42CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD42Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD42Cut_layer0)
    (by decide +kernel) scD42Cut_caps_nonneg scD42Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD43CutCell) (roots := scD43CutRoots)
    (caps := scD43CutCaps) (weightFloor := scD43CutWeightFloor) (margins := scD43CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD43Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD43Cut_layer0)
    (by decide +kernel) scD43Cut_caps_nonneg scD43Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD44CutCell) (roots := scD44CutRoots)
    (caps := scD44CutCaps) (weightFloor := scD44CutWeightFloor) (margins := scD44CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD44Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD44Cut_layer0)
    (by decide +kernel) scD44Cut_caps_nonneg scD44Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD45CutCell) (roots := scD45CutRoots)
    (caps := scD45CutCaps) (weightFloor := scD45CutWeightFloor) (margins := scD45CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD45Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD45Cut_layer0)
    (by decide +kernel) scD45Cut_caps_nonneg scD45Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD46CutCell) (roots := scD46CutRoots)
    (caps := scD46CutCaps) (weightFloor := scD46CutWeightFloor) (margins := scD46CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD46Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD46Cut_layer0)
    (by decide +kernel) scD46Cut_caps_nonneg scD46Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD47CutCell) (roots := scD47CutRoots)
    (caps := scD47CutCaps) (weightFloor := scD47CutWeightFloor) (margins := scD47CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD47Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD47Cut_layer0)
    (by decide +kernel) scD47Cut_caps_nonneg scD47Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD48CutCell) (roots := scD48CutRoots)
    (caps := scD48CutCaps) (weightFloor := scD48CutWeightFloor) (margins := scD48CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD48Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD48Cut_layer0)
    (by decide +kernel) scD48Cut_caps_nonneg scD48Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD49CutCell) (roots := scD49CutRoots)
    (caps := scD49CutCaps) (weightFloor := scD49CutWeightFloor) (margins := scD49CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD49Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD49Cut_layer0)
    (by decide +kernel) scD49Cut_caps_nonneg scD49Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD50CutCell) (roots := scD50CutRoots)
    (caps := scD50CutCaps) (weightFloor := scD50CutWeightFloor) (margins := scD50CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD50Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD50Cut_layer0)
    (by decide +kernel) scD50Cut_caps_nonneg scD50Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD51CutCell) (roots := scD51CutRoots)
    (caps := scD51CutCaps) (weightFloor := scD51CutWeightFloor) (margins := scD51CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD51Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD51Cut_layer0)
    (by decide +kernel) scD51Cut_caps_nonneg scD51Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates256 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scD52CutCell) (roots := scD52CutRoots)
    (caps := scD52CutCaps) (weightFloor := scD52CutWeightFloor) (margins := scD52CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD52Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD52Cut_layer0)
    (by decide +kernel) scD52Cut_caps_nonneg scD52Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD53CutCell) (roots := scD53CutRoots)
    (caps := scD53CutCaps) (weightFloor := scD53CutWeightFloor) (margins := scD53CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD53Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD53Cut_layer0)
    (by decide +kernel) scD53Cut_caps_nonneg scD53Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD54CutCell) (roots := scD54CutRoots)
    (caps := scD54CutCaps) (weightFloor := scD54CutWeightFloor) (margins := scD54CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD54Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD54Cut_layer0)
    (by decide +kernel) scD54Cut_caps_nonneg scD54Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD55CutCell) (roots := scD55CutRoots)
    (caps := scD55CutCaps) (weightFloor := scD55CutWeightFloor) (margins := scD55CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD55Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD55Cut_layer0)
    (by decide +kernel) scD55Cut_caps_nonneg scD55Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD56CutCell) (roots := scD56CutRoots)
    (caps := scD56CutCaps) (weightFloor := scD56CutWeightFloor) (margins := scD56CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD56Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD56Cut_layer0)
    (by decide +kernel) scD56Cut_caps_nonneg scD56Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD57CutCell) (roots := scD57CutRoots)
    (caps := scD57CutCaps) (weightFloor := scD57CutWeightFloor) (margins := scD57CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD57Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD57Cut_layer0)
    (by decide +kernel) scD57Cut_caps_nonneg scD57Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD58CutCell) (roots := scD58CutRoots)
    (caps := scD58CutCaps) (weightFloor := scD58CutWeightFloor) (margins := scD58CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD58Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD58Cut_layer0)
    (by decide +kernel) scD58Cut_caps_nonneg scD58Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD59CutCell) (roots := scD59CutRoots)
    (caps := scD59CutCaps) (weightFloor := scD59CutWeightFloor) (margins := scD59CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD59Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD59Cut_layer0)
    (by decide +kernel) scD59Cut_caps_nonneg scD59Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD60CutCell) (roots := scD60CutRoots)
    (caps := scD60CutCaps) (weightFloor := scD60CutWeightFloor) (margins := scD60CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD60Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD60Cut_layer0)
    (by decide +kernel) scD60Cut_caps_nonneg scD60Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD61CutCell) (roots := scD61CutRoots)
    (caps := scD61CutCaps) (weightFloor := scD61CutWeightFloor) (margins := scD61CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD61Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD61Cut_layer0)
    (by decide +kernel) scD61Cut_caps_nonneg scD61Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD62CutCell) (roots := scD62CutRoots)
    (caps := scD62CutCaps) (weightFloor := scD62CutWeightFloor) (margins := scD62CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD62Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD62Cut_layer0)
    (by decide +kernel) scD62Cut_caps_nonneg scD62Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD63CutCell) (roots := scD63CutRoots)
    (caps := scD63CutCaps) (weightFloor := scD63CutWeightFloor) (margins := scD63CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD63Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD63Cut_layer0)
    (by decide +kernel) scD63Cut_caps_nonneg scD63Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD64CutCell) (roots := scD64CutRoots)
    (caps := scD64CutCaps) (weightFloor := scD64CutWeightFloor) (margins := scD64CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD64Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD64Cut_layer0)
    (by decide +kernel) scD64Cut_caps_nonneg scD64Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD65CutCell) (roots := scD65CutRoots)
    (caps := scD65CutCaps) (weightFloor := scD65CutWeightFloor) (margins := scD65CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD65Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD65Cut_layer0)
    (by decide +kernel) scD65Cut_caps_nonneg scD65Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD66CutCell) (roots := scD66CutRoots)
    (caps := scD66CutCaps) (weightFloor := scD66CutWeightFloor) (margins := scD66CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD66Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD66Cut_layer0)
    (by decide +kernel) scD66Cut_caps_nonneg scD66Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD67CutCell) (roots := scD67CutRoots)
    (caps := scD67CutCaps) (weightFloor := scD67CutWeightFloor) (margins := scD67CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD67Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD67Cut_layer0)
    (by decide +kernel) scD67Cut_caps_nonneg scD67Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD68CutCell) (roots := scD68CutRoots)
    (caps := scD68CutCaps) (weightFloor := scD68CutWeightFloor) (margins := scD68CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD68Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD68Cut_layer0)
    (by decide +kernel) scD68Cut_caps_nonneg scD68Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD69CutCell) (roots := scD69CutRoots)
    (caps := scD69CutCaps) (weightFloor := scD69CutWeightFloor) (margins := scD69CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD69Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD69Cut_layer0)
    (by decide +kernel) scD69Cut_caps_nonneg scD69Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD70CutCell) (roots := scD70CutRoots)
    (caps := scD70CutCaps) (weightFloor := scD70CutWeightFloor) (margins := scD70CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD70Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD70Cut_layer0)
    (by decide +kernel) scD70Cut_caps_nonneg scD70Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD71CutCell) (roots := scD71CutRoots)
    (caps := scD71CutCaps) (weightFloor := scD71CutWeightFloor) (margins := scD71CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD71Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD71Cut_layer0)
    (by decide +kernel) scD71Cut_caps_nonneg scD71Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD72CutCell) (roots := scD72CutRoots)
    (caps := scD72CutCaps) (weightFloor := scD72CutWeightFloor) (margins := scD72CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD72Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD72Cut_layer0)
    (by decide +kernel) scD72Cut_caps_nonneg scD72Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD73CutCell) (roots := scD73CutRoots)
    (caps := scD73CutCaps) (weightFloor := scD73CutWeightFloor) (margins := scD73CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD73Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD73Cut_layer0)
    (by decide +kernel) scD73Cut_caps_nonneg scD73Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD74CutCell) (roots := scD74CutRoots)
    (caps := scD74CutCaps) (weightFloor := scD74CutWeightFloor) (margins := scD74CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD74Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD74Cut_layer0)
    (by decide +kernel) scD74Cut_caps_nonneg scD74Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD75CutCell) (roots := scD75CutRoots)
    (caps := scD75CutCaps) (weightFloor := scD75CutWeightFloor) (margins := scD75CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD75Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD75Cut_layer0)
    (by decide +kernel) scD75Cut_caps_nonneg scD75Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD76CutCell) (roots := scD76CutRoots)
    (caps := scD76CutCaps) (weightFloor := scD76CutWeightFloor) (margins := scD76CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD76Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD76Cut_layer0)
    (by decide +kernel) scD76Cut_caps_nonneg scD76Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD77CutCell) (roots := scD77CutRoots)
    (caps := scD77CutCaps) (weightFloor := scD77CutWeightFloor) (margins := scD77CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD77Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD77Cut_layer0)
    (by decide +kernel) scD77Cut_caps_nonneg scD77Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD78CutCell) (roots := scD78CutRoots)
    (caps := scD78CutCaps) (weightFloor := scD78CutWeightFloor) (margins := scD78CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD78Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD78Cut_layer0)
    (by decide +kernel) scD78Cut_caps_nonneg scD78Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD79CutCell) (roots := scD79CutRoots)
    (caps := scD79CutCaps) (weightFloor := scD79CutWeightFloor) (margins := scD79CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD79Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD79Cut_layer0)
    (by decide +kernel) scD79Cut_caps_nonneg scD79Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD80CutCell) (roots := scD80CutRoots)
    (caps := scD80CutCaps) (weightFloor := scD80CutWeightFloor) (margins := scD80CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD80Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD80Cut_layer0)
    (by decide +kernel) scD80Cut_caps_nonneg scD80Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD81CutCell) (roots := scD81CutRoots)
    (caps := scD81CutCaps) (weightFloor := scD81CutWeightFloor) (margins := scD81CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD81Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD81Cut_layer0)
    (by decide +kernel) scD81Cut_caps_nonneg scD81Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD82CutCell) (roots := scD82CutRoots)
    (caps := scD82CutCaps) (weightFloor := scD82CutWeightFloor) (margins := scD82CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD82Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD82Cut_layer0)
    (by decide +kernel) scD82Cut_caps_nonneg scD82Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD83CutCell) (roots := scD83CutRoots)
    (caps := scD83CutCaps) (weightFloor := scD83CutWeightFloor) (margins := scD83CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD83Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD83Cut_layer0)
    (by decide +kernel) scD83Cut_caps_nonneg scD83Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates288 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scD84CutCell) (roots := scD84CutRoots)
    (caps := scD84CutCaps) (weightFloor := scD84CutWeightFloor) (margins := scD84CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD84Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD84Cut_layer0)
    (by decide +kernel) scD84Cut_caps_nonneg scD84Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD85CutCell) (roots := scD85CutRoots)
    (caps := scD85CutCaps) (weightFloor := scD85CutWeightFloor) (margins := scD85CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD85Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD85Cut_layer0)
    (by decide +kernel) scD85Cut_caps_nonneg scD85Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD86CutCell) (roots := scD86CutRoots)
    (caps := scD86CutCaps) (weightFloor := scD86CutWeightFloor) (margins := scD86CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD86Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD86Cut_layer0)
    (by decide +kernel) scD86Cut_caps_nonneg scD86Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD87CutCell) (roots := scD87CutRoots)
    (caps := scD87CutCaps) (weightFloor := scD87CutWeightFloor) (margins := scD87CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD87Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD87Cut_layer0)
    (by decide +kernel) scD87Cut_caps_nonneg scD87Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD88CutCell) (roots := scD88CutRoots)
    (caps := scD88CutCaps) (weightFloor := scD88CutWeightFloor) (margins := scD88CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD88Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD88Cut_layer0)
    (by decide +kernel) scD88Cut_caps_nonneg scD88Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD89CutCell) (roots := scD89CutRoots)
    (caps := scD89CutCaps) (weightFloor := scD89CutWeightFloor) (margins := scD89CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD89Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD89Cut_layer0)
    (by decide +kernel) scD89Cut_caps_nonneg scD89Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD90CutCell) (roots := scD90CutRoots)
    (caps := scD90CutCaps) (weightFloor := scD90CutWeightFloor) (margins := scD90CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD90Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD90Cut_layer0)
    (by decide +kernel) scD90Cut_caps_nonneg scD90Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD91CutCell) (roots := scD91CutRoots)
    (caps := scD91CutCaps) (weightFloor := scD91CutWeightFloor) (margins := scD91CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD91Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD91Cut_layer0)
    (by decide +kernel) scD91Cut_caps_nonneg scD91Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD92CutCell) (roots := scD92CutRoots)
    (caps := scD92CutCaps) (weightFloor := scD92CutWeightFloor) (margins := scD92CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD92Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD92Cut_layer0)
    (by decide +kernel) scD92Cut_caps_nonneg scD92Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD93CutCell) (roots := scD93CutRoots)
    (caps := scD93CutCaps) (weightFloor := scD93CutWeightFloor) (margins := scD93CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD93Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD93Cut_layer0)
    (by decide +kernel) scD93Cut_caps_nonneg scD93Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD94CutCell) (roots := scD94CutRoots)
    (caps := scD94CutCaps) (weightFloor := scD94CutWeightFloor) (margins := scD94CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD94Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD94Cut_layer0)
    (by decide +kernel) scD94Cut_caps_nonneg scD94Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD95CutCell) (roots := scD95CutRoots)
    (caps := scD95CutCaps) (weightFloor := scD95CutWeightFloor) (margins := scD95CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD95Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD95Cut_layer0)
    (by decide +kernel) scD95Cut_caps_nonneg scD95Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD96CutCell) (roots := scD96CutRoots)
    (caps := scD96CutCaps) (weightFloor := scD96CutWeightFloor) (margins := scD96CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD96Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD96Cut_layer0)
    (by decide +kernel) scD96Cut_caps_nonneg scD96Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD97CutCell) (roots := scD97CutRoots)
    (caps := scD97CutCaps) (weightFloor := scD97CutWeightFloor) (margins := scD97CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD97Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD97Cut_layer0)
    (by decide +kernel) scD97Cut_caps_nonneg scD97Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD98CutCell) (roots := scD98CutRoots)
    (caps := scD98CutCaps) (weightFloor := scD98CutWeightFloor) (margins := scD98CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD98Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD98Cut_layer0)
    (by decide +kernel) scD98Cut_caps_nonneg scD98Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD99CutCell) (roots := scD99CutRoots)
    (caps := scD99CutCaps) (weightFloor := scD99CutWeightFloor) (margins := scD99CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD99Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD99Cut_layer0)
    (by decide +kernel) scD99Cut_caps_nonneg scD99Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD100CutCell) (roots := scD100CutRoots)
    (caps := scD100CutCaps) (weightFloor := scD100CutWeightFloor) (margins := scD100CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD100Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD100Cut_layer0)
    (by decide +kernel) scD100Cut_caps_nonneg scD100Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scD101CutCell) (roots := scD101CutRoots)
    (caps := scD101CutCaps) (weightFloor := scD101CutWeightFloor) (margins := scD101CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scD101Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scD101Cut_layer0)
    (by decide +kernel) scD101Cut_caps_nonneg scD101Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE0CutCell) (roots := scE0CutRoots)
    (caps := scE0CutCaps) (weightFloor := scE0CutWeightFloor) (margins := scE0CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE0Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE0Cut_layer0)
    (by decide +kernel) scE0Cut_caps_nonneg scE0Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE1CutCell) (roots := scE1CutRoots)
    (caps := scE1CutCaps) (weightFloor := scE1CutWeightFloor) (margins := scE1CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE1Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE1Cut_layer0)
    (by decide +kernel) scE1Cut_caps_nonneg scE1Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE2CutCell) (roots := scE2CutRoots)
    (caps := scE2CutCaps) (weightFloor := scE2CutWeightFloor) (margins := scE2CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE2Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE2Cut_layer0)
    (by decide +kernel) scE2Cut_caps_nonneg scE2Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE3CutCell) (roots := scE3CutRoots)
    (caps := scE3CutCaps) (weightFloor := scE3CutWeightFloor) (margins := scE3CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE3Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE3Cut_layer0)
    (by decide +kernel) scE3Cut_caps_nonneg scE3Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE4CutCell) (roots := scE4CutRoots)
    (caps := scE4CutCaps) (weightFloor := scE4CutWeightFloor) (margins := scE4CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE4Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE4Cut_layer0)
    (by decide +kernel) scE4Cut_caps_nonneg scE4Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE5CutCell) (roots := scE5CutRoots)
    (caps := scE5CutCaps) (weightFloor := scE5CutWeightFloor) (margins := scE5CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE5Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE5Cut_layer0)
    (by decide +kernel) scE5Cut_caps_nonneg scE5Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE6CutCell) (roots := scE6CutRoots)
    (caps := scE6CutCaps) (weightFloor := scE6CutWeightFloor) (margins := scE6CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE6Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE6Cut_layer0)
    (by decide +kernel) scE6Cut_caps_nonneg scE6Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE7CutCell) (roots := scE7CutRoots)
    (caps := scE7CutCaps) (weightFloor := scE7CutWeightFloor) (margins := scE7CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE7Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE7Cut_layer0)
    (by decide +kernel) scE7Cut_caps_nonneg scE7Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE8CutCell) (roots := scE8CutRoots)
    (caps := scE8CutCaps) (weightFloor := scE8CutWeightFloor) (margins := scE8CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE8Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE8Cut_layer0)
    (by decide +kernel) scE8Cut_caps_nonneg scE8Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE9CutCell) (roots := scE9CutRoots)
    (caps := scE9CutCaps) (weightFloor := scE9CutWeightFloor) (margins := scE9CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE9Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE9Cut_layer0)
    (by decide +kernel) scE9Cut_caps_nonneg scE9Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE10CutCell) (roots := scE10CutRoots)
    (caps := scE10CutCaps) (weightFloor := scE10CutWeightFloor) (margins := scE10CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE10Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE10Cut_layer0)
    (by decide +kernel) scE10Cut_caps_nonneg scE10Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE11CutCell) (roots := scE11CutRoots)
    (caps := scE11CutCaps) (weightFloor := scE11CutWeightFloor) (margins := scE11CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE11Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE11Cut_layer0)
    (by decide +kernel) scE11Cut_caps_nonneg scE11Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE12CutCell) (roots := scE12CutRoots)
    (caps := scE12CutCaps) (weightFloor := scE12CutWeightFloor) (margins := scE12CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE12Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE12Cut_layer0)
    (by decide +kernel) scE12Cut_caps_nonneg scE12Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE13CutCell) (roots := scE13CutRoots)
    (caps := scE13CutCaps) (weightFloor := scE13CutWeightFloor) (margins := scE13CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE13Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE13Cut_layer0)
    (by decide +kernel) scE13Cut_caps_nonneg scE13Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates320 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scE14CutCell) (roots := scE14CutRoots)
    (caps := scE14CutCaps) (weightFloor := scE14CutWeightFloor) (margins := scE14CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE14Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE14Cut_layer0)
    (by decide +kernel) scE14Cut_caps_nonneg scE14Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE15CutCell) (roots := scE15CutRoots)
    (caps := scE15CutCaps) (weightFloor := scE15CutWeightFloor) (margins := scE15CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE15Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE15Cut_layer0)
    (by decide +kernel) scE15Cut_caps_nonneg scE15Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE16CutCell) (roots := scE16CutRoots)
    (caps := scE16CutCaps) (weightFloor := scE16CutWeightFloor) (margins := scE16CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE16Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE16Cut_layer0)
    (by decide +kernel) scE16Cut_caps_nonneg scE16Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE17CutCell) (roots := scE17CutRoots)
    (caps := scE17CutCaps) (weightFloor := scE17CutWeightFloor) (margins := scE17CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE17Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE17Cut_layer0)
    (by decide +kernel) scE17Cut_caps_nonneg scE17Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE18CutCell) (roots := scE18CutRoots)
    (caps := scE18CutCaps) (weightFloor := scE18CutWeightFloor) (margins := scE18CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE18Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE18Cut_layer0)
    (by decide +kernel) scE18Cut_caps_nonneg scE18Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE19CutCell) (roots := scE19CutRoots)
    (caps := scE19CutCaps) (weightFloor := scE19CutWeightFloor) (margins := scE19CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE19Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE19Cut_layer0)
    (by decide +kernel) scE19Cut_caps_nonneg scE19Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE20CutCell) (roots := scE20CutRoots)
    (caps := scE20CutCaps) (weightFloor := scE20CutWeightFloor) (margins := scE20CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE20Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE20Cut_layer0)
    (by decide +kernel) scE20Cut_caps_nonneg scE20Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE21CutCell) (roots := scE21CutRoots)
    (caps := scE21CutCaps) (weightFloor := scE21CutWeightFloor) (margins := scE21CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE21Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE21Cut_layer0)
    (by decide +kernel) scE21Cut_caps_nonneg scE21Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE22CutCell) (roots := scE22CutRoots)
    (caps := scE22CutCaps) (weightFloor := scE22CutWeightFloor) (margins := scE22CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE22Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE22Cut_layer0)
    (by decide +kernel) scE22Cut_caps_nonneg scE22Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE23CutCell) (roots := scE23CutRoots)
    (caps := scE23CutCaps) (weightFloor := scE23CutWeightFloor) (margins := scE23CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE23Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE23Cut_layer0)
    (by decide +kernel) scE23Cut_caps_nonneg scE23Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE24CutCell) (roots := scE24CutRoots)
    (caps := scE24CutCaps) (weightFloor := scE24CutWeightFloor) (margins := scE24CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE24Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE24Cut_layer0)
    (by decide +kernel) scE24Cut_caps_nonneg scE24Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE25CutCell) (roots := scE25CutRoots)
    (caps := scE25CutCaps) (weightFloor := scE25CutWeightFloor) (margins := scE25CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE25Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE25Cut_layer0)
    (by decide +kernel) scE25Cut_caps_nonneg scE25Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE26CutCell) (roots := scE26CutRoots)
    (caps := scE26CutCaps) (weightFloor := scE26CutWeightFloor) (margins := scE26CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE26Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE26Cut_layer0)
    (by decide +kernel) scE26Cut_caps_nonneg scE26Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE27CutCell) (roots := scE27CutRoots)
    (caps := scE27CutCaps) (weightFloor := scE27CutWeightFloor) (margins := scE27CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE27Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE27Cut_layer0)
    (by decide +kernel) scE27Cut_caps_nonneg scE27Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE28CutCell) (roots := scE28CutRoots)
    (caps := scE28CutCaps) (weightFloor := scE28CutWeightFloor) (margins := scE28CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE28Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE28Cut_layer0)
    (by decide +kernel) scE28Cut_caps_nonneg scE28Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE29CutCell) (roots := scE29CutRoots)
    (caps := scE29CutCaps) (weightFloor := scE29CutWeightFloor) (margins := scE29CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE29Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE29Cut_layer0)
    (by decide +kernel) scE29Cut_caps_nonneg scE29Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE30CutCell) (roots := scE30CutRoots)
    (caps := scE30CutCaps) (weightFloor := scE30CutWeightFloor) (margins := scE30CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE30Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE30Cut_layer0)
    (by decide +kernel) scE30Cut_caps_nonneg scE30Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE31CutCell) (roots := scE31CutRoots)
    (caps := scE31CutCaps) (weightFloor := scE31CutWeightFloor) (margins := scE31CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE31Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE31Cut_layer0)
    (by decide +kernel) scE31Cut_caps_nonneg scE31Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE32CutCell) (roots := scE32CutRoots)
    (caps := scE32CutCaps) (weightFloor := scE32CutWeightFloor) (margins := scE32CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE32Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE32Cut_layer0)
    (by decide +kernel) scE32Cut_caps_nonneg scE32Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE33CutCell) (roots := scE33CutRoots)
    (caps := scE33CutCaps) (weightFloor := scE33CutWeightFloor) (margins := scE33CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE33Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE33Cut_layer0)
    (by decide +kernel) scE33Cut_caps_nonneg scE33Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE34CutCell) (roots := scE34CutRoots)
    (caps := scE34CutCaps) (weightFloor := scE34CutWeightFloor) (margins := scE34CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE34Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE34Cut_layer0)
    (by decide +kernel) scE34Cut_caps_nonneg scE34Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE35CutCell) (roots := scE35CutRoots)
    (caps := scE35CutCaps) (weightFloor := scE35CutWeightFloor) (margins := scE35CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE35Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE35Cut_layer0)
    (by decide +kernel) scE35Cut_caps_nonneg scE35Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE36CutCell) (roots := scE36CutRoots)
    (caps := scE36CutCaps) (weightFloor := scE36CutWeightFloor) (margins := scE36CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE36Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE36Cut_layer0)
    (by decide +kernel) scE36Cut_caps_nonneg scE36Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE37CutCell) (roots := scE37CutRoots)
    (caps := scE37CutCaps) (weightFloor := scE37CutWeightFloor) (margins := scE37CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE37Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE37Cut_layer0)
    (by decide +kernel) scE37Cut_caps_nonneg scE37Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE38CutCell) (roots := scE38CutRoots)
    (caps := scE38CutCaps) (weightFloor := scE38CutWeightFloor) (margins := scE38CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE38Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE38Cut_layer0)
    (by decide +kernel) scE38Cut_caps_nonneg scE38Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE39CutCell) (roots := scE39CutRoots)
    (caps := scE39CutCaps) (weightFloor := scE39CutWeightFloor) (margins := scE39CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE39Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE39Cut_layer0)
    (by decide +kernel) scE39Cut_caps_nonneg scE39Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE40CutCell) (roots := scE40CutRoots)
    (caps := scE40CutCaps) (weightFloor := scE40CutWeightFloor) (margins := scE40CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE40Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE40Cut_layer0)
    (by decide +kernel) scE40Cut_caps_nonneg scE40Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE41CutCell) (roots := scE41CutRoots)
    (caps := scE41CutCaps) (weightFloor := scE41CutWeightFloor) (margins := scE41CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE41Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE41Cut_layer0)
    (by decide +kernel) scE41Cut_caps_nonneg scE41Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE42CutCell) (roots := scE42CutRoots)
    (caps := scE42CutCaps) (weightFloor := scE42CutWeightFloor) (margins := scE42CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE42Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE42Cut_layer0)
    (by decide +kernel) scE42Cut_caps_nonneg scE42Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE43CutCell) (roots := scE43CutRoots)
    (caps := scE43CutCaps) (weightFloor := scE43CutWeightFloor) (margins := scE43CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE43Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE43Cut_layer0)
    (by decide +kernel) scE43Cut_caps_nonneg scE43Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE44CutCell) (roots := scE44CutRoots)
    (caps := scE44CutCaps) (weightFloor := scE44CutWeightFloor) (margins := scE44CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE44Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE44Cut_layer0)
    (by decide +kernel) scE44Cut_caps_nonneg scE44Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE45CutCell) (roots := scE45CutRoots)
    (caps := scE45CutCaps) (weightFloor := scE45CutWeightFloor) (margins := scE45CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE45Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE45Cut_layer0)
    (by decide +kernel) scE45Cut_caps_nonneg scE45Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates352 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scE46CutCell) (roots := scE46CutRoots)
    (caps := scE46CutCaps) (weightFloor := scE46CutWeightFloor) (margins := scE46CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE46Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE46Cut_layer0)
    (by decide +kernel) scE46Cut_caps_nonneg scE46Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE47CutCell) (roots := scE47CutRoots)
    (caps := scE47CutCaps) (weightFloor := scE47CutWeightFloor) (margins := scE47CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE47Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE47Cut_layer0)
    (by decide +kernel) scE47Cut_caps_nonneg scE47Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE48CutCell) (roots := scE48CutRoots)
    (caps := scE48CutCaps) (weightFloor := scE48CutWeightFloor) (margins := scE48CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE48Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE48Cut_layer0)
    (by decide +kernel) scE48Cut_caps_nonneg scE48Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE49CutCell) (roots := scE49CutRoots)
    (caps := scE49CutCaps) (weightFloor := scE49CutWeightFloor) (margins := scE49CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE49Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE49Cut_layer0)
    (by decide +kernel) scE49Cut_caps_nonneg scE49Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE50CutCell) (roots := scE50CutRoots)
    (caps := scE50CutCaps) (weightFloor := scE50CutWeightFloor) (margins := scE50CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE50Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE50Cut_layer0)
    (by decide +kernel) scE50Cut_caps_nonneg scE50Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE51CutCell) (roots := scE51CutRoots)
    (caps := scE51CutCaps) (weightFloor := scE51CutWeightFloor) (margins := scE51CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE51Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE51Cut_layer0)
    (by decide +kernel) scE51Cut_caps_nonneg scE51Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE52CutCell) (roots := scE52CutRoots)
    (caps := scE52CutCaps) (weightFloor := scE52CutWeightFloor) (margins := scE52CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE52Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE52Cut_layer0)
    (by decide +kernel) scE52Cut_caps_nonneg scE52Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE53CutCell) (roots := scE53CutRoots)
    (caps := scE53CutCaps) (weightFloor := scE53CutWeightFloor) (margins := scE53CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE53Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE53Cut_layer0)
    (by decide +kernel) scE53Cut_caps_nonneg scE53Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE54CutCell) (roots := scE54CutRoots)
    (caps := scE54CutCaps) (weightFloor := scE54CutWeightFloor) (margins := scE54CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE54Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE54Cut_layer0)
    (by decide +kernel) scE54Cut_caps_nonneg scE54Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE55CutCell) (roots := scE55CutRoots)
    (caps := scE55CutCaps) (weightFloor := scE55CutWeightFloor) (margins := scE55CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE55Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE55Cut_layer0)
    (by decide +kernel) scE55Cut_caps_nonneg scE55Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE56CutCell) (roots := scE56CutRoots)
    (caps := scE56CutCaps) (weightFloor := scE56CutWeightFloor) (margins := scE56CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE56Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE56Cut_layer0)
    (by decide +kernel) scE56Cut_caps_nonneg scE56Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE57CutCell) (roots := scE57CutRoots)
    (caps := scE57CutCaps) (weightFloor := scE57CutWeightFloor) (margins := scE57CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE57Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE57Cut_layer0)
    (by decide +kernel) scE57Cut_caps_nonneg scE57Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE58CutCell) (roots := scE58CutRoots)
    (caps := scE58CutCaps) (weightFloor := scE58CutWeightFloor) (margins := scE58CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE58Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE58Cut_layer0)
    (by decide +kernel) scE58Cut_caps_nonneg scE58Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE59CutCell) (roots := scE59CutRoots)
    (caps := scE59CutCaps) (weightFloor := scE59CutWeightFloor) (margins := scE59CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE59Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE59Cut_layer0)
    (by decide +kernel) scE59Cut_caps_nonneg scE59Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE60CutCell) (roots := scE60CutRoots)
    (caps := scE60CutCaps) (weightFloor := scE60CutWeightFloor) (margins := scE60CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE60Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE60Cut_layer0)
    (by decide +kernel) scE60Cut_caps_nonneg scE60Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE61CutCell) (roots := scE61CutRoots)
    (caps := scE61CutCaps) (weightFloor := scE61CutWeightFloor) (margins := scE61CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE61Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE61Cut_layer0)
    (by decide +kernel) scE61Cut_caps_nonneg scE61Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE62CutCell) (roots := scE62CutRoots)
    (caps := scE62CutCaps) (weightFloor := scE62CutWeightFloor) (margins := scE62CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE62Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE62Cut_layer0)
    (by decide +kernel) scE62Cut_caps_nonneg scE62Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE63CutCell) (roots := scE63CutRoots)
    (caps := scE63CutCaps) (weightFloor := scE63CutWeightFloor) (margins := scE63CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE63Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE63Cut_layer0)
    (by decide +kernel) scE63Cut_caps_nonneg scE63Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE64CutCell) (roots := scE64CutRoots)
    (caps := scE64CutCaps) (weightFloor := scE64CutWeightFloor) (margins := scE64CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE64Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE64Cut_layer0)
    (by decide +kernel) scE64Cut_caps_nonneg scE64Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE65CutCell) (roots := scE65CutRoots)
    (caps := scE65CutCaps) (weightFloor := scE65CutWeightFloor) (margins := scE65CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE65Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE65Cut_layer0)
    (by decide +kernel) scE65Cut_caps_nonneg scE65Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE66CutCell) (roots := scE66CutRoots)
    (caps := scE66CutCaps) (weightFloor := scE66CutWeightFloor) (margins := scE66CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE66Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE66Cut_layer0)
    (by decide +kernel) scE66Cut_caps_nonneg scE66Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE67CutCell) (roots := scE67CutRoots)
    (caps := scE67CutCaps) (weightFloor := scE67CutWeightFloor) (margins := scE67CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE67Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE67Cut_layer0)
    (by decide +kernel) scE67Cut_caps_nonneg scE67Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE68CutCell) (roots := scE68CutRoots)
    (caps := scE68CutCaps) (weightFloor := scE68CutWeightFloor) (margins := scE68CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE68Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE68Cut_layer0)
    (by decide +kernel) scE68Cut_caps_nonneg scE68Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE69CutCell) (roots := scE69CutRoots)
    (caps := scE69CutCaps) (weightFloor := scE69CutWeightFloor) (margins := scE69CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE69Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE69Cut_layer0)
    (by decide +kernel) scE69Cut_caps_nonneg scE69Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE70CutCell) (roots := scE70CutRoots)
    (caps := scE70CutCaps) (weightFloor := scE70CutWeightFloor) (margins := scE70CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE70Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE70Cut_layer0)
    (by decide +kernel) scE70Cut_caps_nonneg scE70Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE71CutCell) (roots := scE71CutRoots)
    (caps := scE71CutCaps) (weightFloor := scE71CutWeightFloor) (margins := scE71CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE71Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE71Cut_layer0)
    (by decide +kernel) scE71Cut_caps_nonneg scE71Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE72CutCell) (roots := scE72CutRoots)
    (caps := scE72CutCaps) (weightFloor := scE72CutWeightFloor) (margins := scE72CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE72Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE72Cut_layer0)
    (by decide +kernel) scE72Cut_caps_nonneg scE72Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE73CutCell) (roots := scE73CutRoots)
    (caps := scE73CutCaps) (weightFloor := scE73CutWeightFloor) (margins := scE73CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE73Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE73Cut_layer0)
    (by decide +kernel) scE73Cut_caps_nonneg scE73Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE74CutCell) (roots := scE74CutRoots)
    (caps := scE74CutCaps) (weightFloor := scE74CutWeightFloor) (margins := scE74CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE74Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE74Cut_layer0)
    (by decide +kernel) scE74Cut_caps_nonneg scE74Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE75CutCell) (roots := scE75CutRoots)
    (caps := scE75CutCaps) (weightFloor := scE75CutWeightFloor) (margins := scE75CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE75Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE75Cut_layer0)
    (by decide +kernel) scE75Cut_caps_nonneg scE75Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE76CutCell) (roots := scE76CutRoots)
    (caps := scE76CutCaps) (weightFloor := scE76CutWeightFloor) (margins := scE76CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE76Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE76Cut_layer0)
    (by decide +kernel) scE76Cut_caps_nonneg scE76Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE77CutCell) (roots := scE77CutRoots)
    (caps := scE77CutCaps) (weightFloor := scE77CutWeightFloor) (margins := scE77CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE77Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE77Cut_layer0)
    (by decide +kernel) scE77Cut_caps_nonneg scE77Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates384 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scE78CutCell) (roots := scE78CutRoots)
    (caps := scE78CutCaps) (weightFloor := scE78CutWeightFloor) (margins := scE78CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE78Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE78Cut_layer0)
    (by decide +kernel) scE78Cut_caps_nonneg scE78Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE79CutCell) (roots := scE79CutRoots)
    (caps := scE79CutCaps) (weightFloor := scE79CutWeightFloor) (margins := scE79CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE79Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE79Cut_layer0)
    (by decide +kernel) scE79Cut_caps_nonneg scE79Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE80CutCell) (roots := scE80CutRoots)
    (caps := scE80CutCaps) (weightFloor := scE80CutWeightFloor) (margins := scE80CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE80Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE80Cut_layer0)
    (by decide +kernel) scE80Cut_caps_nonneg scE80Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE81CutCell) (roots := scE81CutRoots)
    (caps := scE81CutCaps) (weightFloor := scE81CutWeightFloor) (margins := scE81CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE81Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE81Cut_layer0)
    (by decide +kernel) scE81Cut_caps_nonneg scE81Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE82CutCell) (roots := scE82CutRoots)
    (caps := scE82CutCaps) (weightFloor := scE82CutWeightFloor) (margins := scE82CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE82Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE82Cut_layer0)
    (by decide +kernel) scE82Cut_caps_nonneg scE82Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE83CutCell) (roots := scE83CutRoots)
    (caps := scE83CutCaps) (weightFloor := scE83CutWeightFloor) (margins := scE83CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE83Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE83Cut_layer0)
    (by decide +kernel) scE83Cut_caps_nonneg scE83Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE84CutCell) (roots := scE84CutRoots)
    (caps := scE84CutCaps) (weightFloor := scE84CutWeightFloor) (margins := scE84CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE84Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE84Cut_layer0)
    (by decide +kernel) scE84Cut_caps_nonneg scE84Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE85CutCell) (roots := scE85CutRoots)
    (caps := scE85CutCaps) (weightFloor := scE85CutWeightFloor) (margins := scE85CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE85Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE85Cut_layer0)
    (by decide +kernel) scE85Cut_caps_nonneg scE85Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE86CutCell) (roots := scE86CutRoots)
    (caps := scE86CutCaps) (weightFloor := scE86CutWeightFloor) (margins := scE86CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE86Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE86Cut_layer0)
    (by decide +kernel) scE86Cut_caps_nonneg scE86Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE87CutCell) (roots := scE87CutRoots)
    (caps := scE87CutCaps) (weightFloor := scE87CutWeightFloor) (margins := scE87CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE87Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE87Cut_layer0)
    (by decide +kernel) scE87Cut_caps_nonneg scE87Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE88CutCell) (roots := scE88CutRoots)
    (caps := scE88CutCaps) (weightFloor := scE88CutWeightFloor) (margins := scE88CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE88Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE88Cut_layer0)
    (by decide +kernel) scE88Cut_caps_nonneg scE88Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE89CutCell) (roots := scE89CutRoots)
    (caps := scE89CutCaps) (weightFloor := scE89CutWeightFloor) (margins := scE89CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE89Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE89Cut_layer0)
    (by decide +kernel) scE89Cut_caps_nonneg scE89Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE90CutCell) (roots := scE90CutRoots)
    (caps := scE90CutCaps) (weightFloor := scE90CutWeightFloor) (margins := scE90CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE90Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE90Cut_layer0)
    (by decide +kernel) scE90Cut_caps_nonneg scE90Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE91CutCell) (roots := scE91CutRoots)
    (caps := scE91CutCaps) (weightFloor := scE91CutWeightFloor) (margins := scE91CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE91Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE91Cut_layer0)
    (by decide +kernel) scE91Cut_caps_nonneg scE91Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE92CutCell) (roots := scE92CutRoots)
    (caps := scE92CutCaps) (weightFloor := scE92CutWeightFloor) (margins := scE92CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE92Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE92Cut_layer0)
    (by decide +kernel) scE92Cut_caps_nonneg scE92Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE93CutCell) (roots := scE93CutRoots)
    (caps := scE93CutCaps) (weightFloor := scE93CutWeightFloor) (margins := scE93CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE93Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE93Cut_layer0)
    (by decide +kernel) scE93Cut_caps_nonneg scE93Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE94CutCell) (roots := scE94CutRoots)
    (caps := scE94CutCaps) (weightFloor := scE94CutWeightFloor) (margins := scE94CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE94Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE94Cut_layer0)
    (by decide +kernel) scE94Cut_caps_nonneg scE94Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE95CutCell) (roots := scE95CutRoots)
    (caps := scE95CutCaps) (weightFloor := scE95CutWeightFloor) (margins := scE95CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE95Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE95Cut_layer0)
    (by decide +kernel) scE95Cut_caps_nonneg scE95Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE96CutCell) (roots := scE96CutRoots)
    (caps := scE96CutCaps) (weightFloor := scE96CutWeightFloor) (margins := scE96CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE96Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE96Cut_layer0)
    (by decide +kernel) scE96Cut_caps_nonneg scE96Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE97CutCell) (roots := scE97CutRoots)
    (caps := scE97CutCaps) (weightFloor := scE97CutWeightFloor) (margins := scE97CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE97Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE97Cut_layer0)
    (by decide +kernel) scE97Cut_caps_nonneg scE97Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE98CutCell) (roots := scE98CutRoots)
    (caps := scE98CutCaps) (weightFloor := scE98CutWeightFloor) (margins := scE98CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE98Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE98Cut_layer0)
    (by decide +kernel) scE98Cut_caps_nonneg scE98Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE99CutCell) (roots := scE99CutRoots)
    (caps := scE99CutCaps) (weightFloor := scE99CutWeightFloor) (margins := scE99CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE99Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE99Cut_layer0)
    (by decide +kernel) scE99Cut_caps_nonneg scE99Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE100CutCell) (roots := scE100CutRoots)
    (caps := scE100CutCaps) (weightFloor := scE100CutWeightFloor) (margins := scE100CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE100Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE100Cut_layer0)
    (by decide +kernel) scE100Cut_caps_nonneg scE100Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE101CutCell) (roots := scE101CutRoots)
    (caps := scE101CutCaps) (weightFloor := scE101CutWeightFloor) (margins := scE101CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE101Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE101Cut_layer0)
    (by decide +kernel) scE101Cut_caps_nonneg scE101Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE102CutCell) (roots := scE102CutRoots)
    (caps := scE102CutCaps) (weightFloor := scE102CutWeightFloor) (margins := scE102CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE102Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE102Cut_layer0)
    (by decide +kernel) scE102Cut_caps_nonneg scE102Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE103CutCell) (roots := scE103CutRoots)
    (caps := scE103CutCaps) (weightFloor := scE103CutWeightFloor) (margins := scE103CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE103Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE103Cut_layer0)
    (by decide +kernel) scE103Cut_caps_nonneg scE103Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE104CutCell) (roots := scE104CutRoots)
    (caps := scE104CutCaps) (weightFloor := scE104CutWeightFloor) (margins := scE104CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE104Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE104Cut_layer0)
    (by decide +kernel) scE104Cut_caps_nonneg scE104Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE105CutCell) (roots := scE105CutRoots)
    (caps := scE105CutCaps) (weightFloor := scE105CutWeightFloor) (margins := scE105CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE105Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE105Cut_layer0)
    (by decide +kernel) scE105Cut_caps_nonneg scE105Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE106CutCell) (roots := scE106CutRoots)
    (caps := scE106CutCaps) (weightFloor := scE106CutWeightFloor) (margins := scE106CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE106Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE106Cut_layer0)
    (by decide +kernel) scE106Cut_caps_nonneg scE106Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE107CutCell) (roots := scE107CutRoots)
    (caps := scE107CutCaps) (weightFloor := scE107CutWeightFloor) (margins := scE107CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE107Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE107Cut_layer0)
    (by decide +kernel) scE107Cut_caps_nonneg scE107Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE108CutCell) (roots := scE108CutRoots)
    (caps := scE108CutCaps) (weightFloor := scE108CutWeightFloor) (margins := scE108CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE108Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE108Cut_layer0)
    (by decide +kernel) scE108Cut_caps_nonneg scE108Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE109CutCell) (roots := scE109CutRoots)
    (caps := scE109CutCaps) (weightFloor := scE109CutWeightFloor) (margins := scE109CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE109Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE109Cut_layer0)
    (by decide +kernel) scE109Cut_caps_nonneg scE109Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates416 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scE110CutCell) (roots := scE110CutRoots)
    (caps := scE110CutCaps) (weightFloor := scE110CutWeightFloor) (margins := scE110CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE110Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE110Cut_layer0)
    (by decide +kernel) scE110Cut_caps_nonneg scE110Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE111CutCell) (roots := scE111CutRoots)
    (caps := scE111CutCaps) (weightFloor := scE111CutWeightFloor) (margins := scE111CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE111Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE111Cut_layer0)
    (by decide +kernel) scE111Cut_caps_nonneg scE111Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE112CutCell) (roots := scE112CutRoots)
    (caps := scE112CutCaps) (weightFloor := scE112CutWeightFloor) (margins := scE112CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE112Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE112Cut_layer0)
    (by decide +kernel) scE112Cut_caps_nonneg scE112Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE113CutCell) (roots := scE113CutRoots)
    (caps := scE113CutCaps) (weightFloor := scE113CutWeightFloor) (margins := scE113CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE113Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE113Cut_layer0)
    (by decide +kernel) scE113Cut_caps_nonneg scE113Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE114CutCell) (roots := scE114CutRoots)
    (caps := scE114CutCaps) (weightFloor := scE114CutWeightFloor) (margins := scE114CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE114Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE114Cut_layer0)
    (by decide +kernel) scE114Cut_caps_nonneg scE114Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE115CutCell) (roots := scE115CutRoots)
    (caps := scE115CutCaps) (weightFloor := scE115CutWeightFloor) (margins := scE115CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE115Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE115Cut_layer0)
    (by decide +kernel) scE115Cut_caps_nonneg scE115Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE116CutCell) (roots := scE116CutRoots)
    (caps := scE116CutCaps) (weightFloor := scE116CutWeightFloor) (margins := scE116CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE116Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE116Cut_layer0)
    (by decide +kernel) scE116Cut_caps_nonneg scE116Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE117CutCell) (roots := scE117CutRoots)
    (caps := scE117CutCaps) (weightFloor := scE117CutWeightFloor) (margins := scE117CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE117Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE117Cut_layer0)
    (by decide +kernel) scE117Cut_caps_nonneg scE117Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE118CutCell) (roots := scE118CutRoots)
    (caps := scE118CutCaps) (weightFloor := scE118CutWeightFloor) (margins := scE118CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE118Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE118Cut_layer0)
    (by decide +kernel) scE118Cut_caps_nonneg scE118Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE119CutCell) (roots := scE119CutRoots)
    (caps := scE119CutCaps) (weightFloor := scE119CutWeightFloor) (margins := scE119CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE119Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE119Cut_layer0)
    (by decide +kernel) scE119Cut_caps_nonneg scE119Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE120CutCell) (roots := scE120CutRoots)
    (caps := scE120CutCaps) (weightFloor := scE120CutWeightFloor) (margins := scE120CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE120Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE120Cut_layer0)
    (by decide +kernel) scE120Cut_caps_nonneg scE120Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE121CutCell) (roots := scE121CutRoots)
    (caps := scE121CutCaps) (weightFloor := scE121CutWeightFloor) (margins := scE121CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE121Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE121Cut_layer0)
    (by decide +kernel) scE121Cut_caps_nonneg scE121Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE122CutCell) (roots := scE122CutRoots)
    (caps := scE122CutCaps) (weightFloor := scE122CutWeightFloor) (margins := scE122CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE122Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE122Cut_layer0)
    (by decide +kernel) scE122Cut_caps_nonneg scE122Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE123CutCell) (roots := scE123CutRoots)
    (caps := scE123CutCaps) (weightFloor := scE123CutWeightFloor) (margins := scE123CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE123Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE123Cut_layer0)
    (by decide +kernel) scE123Cut_caps_nonneg scE123Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE124CutCell) (roots := scE124CutRoots)
    (caps := scE124CutCaps) (weightFloor := scE124CutWeightFloor) (margins := scE124CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE124Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE124Cut_layer0)
    (by decide +kernel) scE124Cut_caps_nonneg scE124Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE125CutCell) (roots := scE125CutRoots)
    (caps := scE125CutCaps) (weightFloor := scE125CutWeightFloor) (margins := scE125CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE125Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE125Cut_layer0)
    (by decide +kernel) scE125Cut_caps_nonneg scE125Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE126CutCell) (roots := scE126CutRoots)
    (caps := scE126CutCaps) (weightFloor := scE126CutWeightFloor) (margins := scE126CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE126Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE126Cut_layer0)
    (by decide +kernel) scE126Cut_caps_nonneg scE126Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE127CutCell) (roots := scE127CutRoots)
    (caps := scE127CutCaps) (weightFloor := scE127CutWeightFloor) (margins := scE127CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE127Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE127Cut_layer0)
    (by decide +kernel) scE127Cut_caps_nonneg scE127Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE128CutCell) (roots := scE128CutRoots)
    (caps := scE128CutCaps) (weightFloor := scE128CutWeightFloor) (margins := scE128CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE128Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE128Cut_layer0)
    (by decide +kernel) scE128Cut_caps_nonneg scE128Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE129CutCell) (roots := scE129CutRoots)
    (caps := scE129CutCaps) (weightFloor := scE129CutWeightFloor) (margins := scE129CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE129Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE129Cut_layer0)
    (by decide +kernel) scE129Cut_caps_nonneg scE129Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE130CutCell) (roots := scE130CutRoots)
    (caps := scE130CutCaps) (weightFloor := scE130CutWeightFloor) (margins := scE130CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE130Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE130Cut_layer0)
    (by decide +kernel) scE130Cut_caps_nonneg scE130Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE131CutCell) (roots := scE131CutRoots)
    (caps := scE131CutCaps) (weightFloor := scE131CutWeightFloor) (margins := scE131CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE131Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE131Cut_layer0)
    (by decide +kernel) scE131Cut_caps_nonneg scE131Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE132CutCell) (roots := scE132CutRoots)
    (caps := scE132CutCaps) (weightFloor := scE132CutWeightFloor) (margins := scE132CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE132Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE132Cut_layer0)
    (by decide +kernel) scE132Cut_caps_nonneg scE132Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE133CutCell) (roots := scE133CutRoots)
    (caps := scE133CutCaps) (weightFloor := scE133CutWeightFloor) (margins := scE133CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE133Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE133Cut_layer0)
    (by decide +kernel) scE133Cut_caps_nonneg scE133Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE134CutCell) (roots := scE134CutRoots)
    (caps := scE134CutCaps) (weightFloor := scE134CutWeightFloor) (margins := scE134CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE134Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE134Cut_layer0)
    (by decide +kernel) scE134Cut_caps_nonneg scE134Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE135CutCell) (roots := scE135CutRoots)
    (caps := scE135CutCaps) (weightFloor := scE135CutWeightFloor) (margins := scE135CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE135Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE135Cut_layer0)
    (by decide +kernel) scE135Cut_caps_nonneg scE135Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE136CutCell) (roots := scE136CutRoots)
    (caps := scE136CutCaps) (weightFloor := scE136CutWeightFloor) (margins := scE136CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE136Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE136Cut_layer0)
    (by decide +kernel) scE136Cut_caps_nonneg scE136Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE137CutCell) (roots := scE137CutRoots)
    (caps := scE137CutCaps) (weightFloor := scE137CutWeightFloor) (margins := scE137CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE137Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE137Cut_layer0)
    (by decide +kernel) scE137Cut_caps_nonneg scE137Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE138CutCell) (roots := scE138CutRoots)
    (caps := scE138CutCaps) (weightFloor := scE138CutWeightFloor) (margins := scE138CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE138Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE138Cut_layer0)
    (by decide +kernel) scE138Cut_caps_nonneg scE138Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE139CutCell) (roots := scE139CutRoots)
    (caps := scE139CutCaps) (weightFloor := scE139CutWeightFloor) (margins := scE139CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE139Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE139Cut_layer0)
    (by decide +kernel) scE139Cut_caps_nonneg scE139Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE140CutCell) (roots := scE140CutRoots)
    (caps := scE140CutCaps) (weightFloor := scE140CutWeightFloor) (margins := scE140CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE140Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE140Cut_layer0)
    (by decide +kernel) scE140Cut_caps_nonneg scE140Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE141CutCell) (roots := scE141CutRoots)
    (caps := scE141CutCaps) (weightFloor := scE141CutWeightFloor) (margins := scE141CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE141Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE141Cut_layer0)
    (by decide +kernel) scE141Cut_caps_nonneg scE141Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates448 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scE142CutCell) (roots := scE142CutRoots)
    (caps := scE142CutCaps) (weightFloor := scE142CutWeightFloor) (margins := scE142CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE142Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE142Cut_layer0)
    (by decide +kernel) scE142Cut_caps_nonneg scE142Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE143CutCell) (roots := scE143CutRoots)
    (caps := scE143CutCaps) (weightFloor := scE143CutWeightFloor) (margins := scE143CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE143Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE143Cut_layer0)
    (by decide +kernel) scE143Cut_caps_nonneg scE143Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE144CutCell) (roots := scE144CutRoots)
    (caps := scE144CutCaps) (weightFloor := scE144CutWeightFloor) (margins := scE144CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE144Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE144Cut_layer0)
    (by decide +kernel) scE144Cut_caps_nonneg scE144Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE145CutCell) (roots := scE145CutRoots)
    (caps := scE145CutCaps) (weightFloor := scE145CutWeightFloor) (margins := scE145CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE145Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE145Cut_layer0)
    (by decide +kernel) scE145Cut_caps_nonneg scE145Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE146CutCell) (roots := scE146CutRoots)
    (caps := scE146CutCaps) (weightFloor := scE146CutWeightFloor) (margins := scE146CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE146Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE146Cut_layer0)
    (by decide +kernel) scE146Cut_caps_nonneg scE146Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE147CutCell) (roots := scE147CutRoots)
    (caps := scE147CutCaps) (weightFloor := scE147CutWeightFloor) (margins := scE147CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE147Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE147Cut_layer0)
    (by decide +kernel) scE147Cut_caps_nonneg scE147Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE148CutCell) (roots := scE148CutRoots)
    (caps := scE148CutCaps) (weightFloor := scE148CutWeightFloor) (margins := scE148CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE148Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE148Cut_layer0)
    (by decide +kernel) scE148Cut_caps_nonneg scE148Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE149CutCell) (roots := scE149CutRoots)
    (caps := scE149CutCaps) (weightFloor := scE149CutWeightFloor) (margins := scE149CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE149Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE149Cut_layer0)
    (by decide +kernel) scE149Cut_caps_nonneg scE149Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE150CutCell) (roots := scE150CutRoots)
    (caps := scE150CutCaps) (weightFloor := scE150CutWeightFloor) (margins := scE150CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE150Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE150Cut_layer0)
    (by decide +kernel) scE150Cut_caps_nonneg scE150Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE151CutCell) (roots := scE151CutRoots)
    (caps := scE151CutCaps) (weightFloor := scE151CutWeightFloor) (margins := scE151CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE151Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE151Cut_layer0)
    (by decide +kernel) scE151Cut_caps_nonneg scE151Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE152CutCell) (roots := scE152CutRoots)
    (caps := scE152CutCaps) (weightFloor := scE152CutWeightFloor) (margins := scE152CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE152Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE152Cut_layer0)
    (by decide +kernel) scE152Cut_caps_nonneg scE152Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE153CutCell) (roots := scE153CutRoots)
    (caps := scE153CutCaps) (weightFloor := scE153CutWeightFloor) (margins := scE153CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE153Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE153Cut_layer0)
    (by decide +kernel) scE153Cut_caps_nonneg scE153Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE154CutCell) (roots := scE154CutRoots)
    (caps := scE154CutCaps) (weightFloor := scE154CutWeightFloor) (margins := scE154CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE154Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE154Cut_layer0)
    (by decide +kernel) scE154Cut_caps_nonneg scE154Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE155CutCell) (roots := scE155CutRoots)
    (caps := scE155CutCaps) (weightFloor := scE155CutWeightFloor) (margins := scE155CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE155Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE155Cut_layer0)
    (by decide +kernel) scE155Cut_caps_nonneg scE155Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE156CutCell) (roots := scE156CutRoots)
    (caps := scE156CutCaps) (weightFloor := scE156CutWeightFloor) (margins := scE156CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE156Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE156Cut_layer0)
    (by decide +kernel) scE156Cut_caps_nonneg scE156Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE157CutCell) (roots := scE157CutRoots)
    (caps := scE157CutCaps) (weightFloor := scE157CutWeightFloor) (margins := scE157CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE157Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE157Cut_layer0)
    (by decide +kernel) scE157Cut_caps_nonneg scE157Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE158CutCell) (roots := scE158CutRoots)
    (caps := scE158CutCaps) (weightFloor := scE158CutWeightFloor) (margins := scE158CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE158Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE158Cut_layer0)
    (by decide +kernel) scE158Cut_caps_nonneg scE158Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE159CutCell) (roots := scE159CutRoots)
    (caps := scE159CutCaps) (weightFloor := scE159CutWeightFloor) (margins := scE159CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE159Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE159Cut_layer0)
    (by decide +kernel) scE159Cut_caps_nonneg scE159Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE160CutCell) (roots := scE160CutRoots)
    (caps := scE160CutCaps) (weightFloor := scE160CutWeightFloor) (margins := scE160CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE160Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE160Cut_layer0)
    (by decide +kernel) scE160Cut_caps_nonneg scE160Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE161CutCell) (roots := scE161CutRoots)
    (caps := scE161CutCaps) (weightFloor := scE161CutWeightFloor) (margins := scE161CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE161Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE161Cut_layer0)
    (by decide +kernel) scE161Cut_caps_nonneg scE161Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE162CutCell) (roots := scE162CutRoots)
    (caps := scE162CutCaps) (weightFloor := scE162CutWeightFloor) (margins := scE162CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE162Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE162Cut_layer0)
    (by decide +kernel) scE162Cut_caps_nonneg scE162Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE163CutCell) (roots := scE163CutRoots)
    (caps := scE163CutCaps) (weightFloor := scE163CutWeightFloor) (margins := scE163CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE163Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE163Cut_layer0)
    (by decide +kernel) scE163Cut_caps_nonneg scE163Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE164CutCell) (roots := scE164CutRoots)
    (caps := scE164CutCaps) (weightFloor := scE164CutWeightFloor) (margins := scE164CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE164Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE164Cut_layer0)
    (by decide +kernel) scE164Cut_caps_nonneg scE164Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE165CutCell) (roots := scE165CutRoots)
    (caps := scE165CutCaps) (weightFloor := scE165CutWeightFloor) (margins := scE165CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE165Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE165Cut_layer0)
    (by decide +kernel) scE165Cut_caps_nonneg scE165Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE166CutCell) (roots := scE166CutRoots)
    (caps := scE166CutCaps) (weightFloor := scE166CutWeightFloor) (margins := scE166CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE166Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE166Cut_layer0)
    (by decide +kernel) scE166Cut_caps_nonneg scE166Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE167CutCell) (roots := scE167CutRoots)
    (caps := scE167CutCaps) (weightFloor := scE167CutWeightFloor) (margins := scE167CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE167Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE167Cut_layer0)
    (by decide +kernel) scE167Cut_caps_nonneg scE167Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE168CutCell) (roots := scE168CutRoots)
    (caps := scE168CutCaps) (weightFloor := scE168CutWeightFloor) (margins := scE168CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE168Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE168Cut_layer0)
    (by decide +kernel) scE168Cut_caps_nonneg scE168Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE169CutCell) (roots := scE169CutRoots)
    (caps := scE169CutCaps) (weightFloor := scE169CutWeightFloor) (margins := scE169CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE169Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE169Cut_layer0)
    (by decide +kernel) scE169Cut_caps_nonneg scE169Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE170CutCell) (roots := scE170CutRoots)
    (caps := scE170CutCaps) (weightFloor := scE170CutWeightFloor) (margins := scE170CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE170Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE170Cut_layer0)
    (by decide +kernel) scE170Cut_caps_nonneg scE170Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE171CutCell) (roots := scE171CutRoots)
    (caps := scE171CutCaps) (weightFloor := scE171CutWeightFloor) (margins := scE171CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE171Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE171Cut_layer0)
    (by decide +kernel) scE171Cut_caps_nonneg scE171Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE172CutCell) (roots := scE172CutRoots)
    (caps := scE172CutCaps) (weightFloor := scE172CutWeightFloor) (margins := scE172CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE172Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE172Cut_layer0)
    (by decide +kernel) scE172Cut_caps_nonneg scE172Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE173CutCell) (roots := scE173CutRoots)
    (caps := scE173CutCaps) (weightFloor := scE173CutWeightFloor) (margins := scE173CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE173Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE173Cut_layer0)
    (by decide +kernel) scE173Cut_caps_nonneg scE173Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates480 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := scE174CutCell) (roots := scE174CutRoots)
    (caps := scE174CutCaps) (weightFloor := scE174CutWeightFloor) (margins := scE174CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE174Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE174Cut_layer0)
    (by decide +kernel) scE174Cut_caps_nonneg scE174Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE175CutCell) (roots := scE175CutRoots)
    (caps := scE175CutCaps) (weightFloor := scE175CutWeightFloor) (margins := scE175CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE175Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE175Cut_layer0)
    (by decide +kernel) scE175Cut_caps_nonneg scE175Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE176CutCell) (roots := scE176CutRoots)
    (caps := scE176CutCaps) (weightFloor := scE176CutWeightFloor) (margins := scE176CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE176Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE176Cut_layer0)
    (by decide +kernel) scE176Cut_caps_nonneg scE176Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE177CutCell) (roots := scE177CutRoots)
    (caps := scE177CutCaps) (weightFloor := scE177CutWeightFloor) (margins := scE177CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE177Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE177Cut_layer0)
    (by decide +kernel) scE177Cut_caps_nonneg scE177Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE178CutCell) (roots := scE178CutRoots)
    (caps := scE178CutCaps) (weightFloor := scE178CutWeightFloor) (margins := scE178CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE178Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE178Cut_layer0)
    (by decide +kernel) scE178Cut_caps_nonneg scE178Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE179CutCell) (roots := scE179CutRoots)
    (caps := scE179CutCaps) (weightFloor := scE179CutWeightFloor) (margins := scE179CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE179Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE179Cut_layer0)
    (by decide +kernel) scE179Cut_caps_nonneg scE179Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE180CutCell) (roots := scE180CutRoots)
    (caps := scE180CutCaps) (weightFloor := scE180CutWeightFloor) (margins := scE180CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE180Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE180Cut_layer0)
    (by decide +kernel) scE180Cut_caps_nonneg scE180Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE181CutCell) (roots := scE181CutRoots)
    (caps := scE181CutCaps) (weightFloor := scE181CutWeightFloor) (margins := scE181CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE181Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE181Cut_layer0)
    (by decide +kernel) scE181Cut_caps_nonneg scE181Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE182CutCell) (roots := scE182CutRoots)
    (caps := scE182CutCaps) (weightFloor := scE182CutWeightFloor) (margins := scE182CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE182Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE182Cut_layer0)
    (by decide +kernel) scE182Cut_caps_nonneg scE182Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE183CutCell) (roots := scE183CutRoots)
    (caps := scE183CutCaps) (weightFloor := scE183CutWeightFloor) (margins := scE183CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE183Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE183Cut_layer0)
    (by decide +kernel) scE183Cut_caps_nonneg scE183Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE184CutCell) (roots := scE184CutRoots)
    (caps := scE184CutCaps) (weightFloor := scE184CutWeightFloor) (margins := scE184CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE184Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE184Cut_layer0)
    (by decide +kernel) scE184Cut_caps_nonneg scE184Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE185CutCell) (roots := scE185CutRoots)
    (caps := scE185CutCaps) (weightFloor := scE185CutWeightFloor) (margins := scE185CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE185Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE185Cut_layer0)
    (by decide +kernel) scE185Cut_caps_nonneg scE185Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE186CutCell) (roots := scE186CutRoots)
    (caps := scE186CutCaps) (weightFloor := scE186CutWeightFloor) (margins := scE186CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE186Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE186Cut_layer0)
    (by decide +kernel) scE186Cut_caps_nonneg scE186Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE187CutCell) (roots := scE187CutRoots)
    (caps := scE187CutCaps) (weightFloor := scE187CutWeightFloor) (margins := scE187CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE187Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE187Cut_layer0)
    (by decide +kernel) scE187Cut_caps_nonneg scE187Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE188CutCell) (roots := scE188CutRoots)
    (caps := scE188CutCaps) (weightFloor := scE188CutWeightFloor) (margins := scE188CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE188Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE188Cut_layer0)
    (by decide +kernel) scE188Cut_caps_nonneg scE188Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE189CutCell) (roots := scE189CutRoots)
    (caps := scE189CutCaps) (weightFloor := scE189CutWeightFloor) (margins := scE189CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE189Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE189Cut_layer0)
    (by decide +kernel) scE189Cut_caps_nonneg scE189Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE190CutCell) (roots := scE190CutRoots)
    (caps := scE190CutCaps) (weightFloor := scE190CutWeightFloor) (margins := scE190CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE190Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE190Cut_layer0)
    (by decide +kernel) scE190Cut_caps_nonneg scE190Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE191CutCell) (roots := scE191CutRoots)
    (caps := scE191CutCaps) (weightFloor := scE191CutWeightFloor) (margins := scE191CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE191Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE191Cut_layer0)
    (by decide +kernel) scE191Cut_caps_nonneg scE191Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE192CutCell) (roots := scE192CutRoots)
    (caps := scE192CutCaps) (weightFloor := scE192CutWeightFloor) (margins := scE192CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE192Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE192Cut_layer0)
    (by decide +kernel) scE192Cut_caps_nonneg scE192Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE193CutCell) (roots := scE193CutRoots)
    (caps := scE193CutCaps) (weightFloor := scE193CutWeightFloor) (margins := scE193CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE193Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE193Cut_layer0)
    (by decide +kernel) scE193Cut_caps_nonneg scE193Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE194CutCell) (roots := scE194CutRoots)
    (caps := scE194CutCaps) (weightFloor := scE194CutWeightFloor) (margins := scE194CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE194Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE194Cut_layer0)
    (by decide +kernel) scE194Cut_caps_nonneg scE194Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE195CutCell) (roots := scE195CutRoots)
    (caps := scE195CutCaps) (weightFloor := scE195CutWeightFloor) (margins := scE195CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE195Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE195Cut_layer0)
    (by decide +kernel) scE195Cut_caps_nonneg scE195Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE196CutCell) (roots := scE196CutRoots)
    (caps := scE196CutCaps) (weightFloor := scE196CutWeightFloor) (margins := scE196CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE196Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE196Cut_layer0)
    (by decide +kernel) scE196Cut_caps_nonneg scE196Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE197CutCell) (roots := scE197CutRoots)
    (caps := scE197CutCaps) (weightFloor := scE197CutWeightFloor) (margins := scE197CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE197Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE197Cut_layer0)
    (by decide +kernel) scE197Cut_caps_nonneg scE197Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE198CutCell) (roots := scE198CutRoots)
    (caps := scE198CutCaps) (weightFloor := scE198CutWeightFloor) (margins := scE198CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE198Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE198Cut_layer0)
    (by decide +kernel) scE198Cut_caps_nonneg scE198Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE199CutCell) (roots := scE199CutRoots)
    (caps := scE199CutCaps) (weightFloor := scE199CutWeightFloor) (margins := scE199CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE199Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE199Cut_layer0)
    (by decide +kernel) scE199Cut_caps_nonneg scE199Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE200CutCell) (roots := scE200CutRoots)
    (caps := scE200CutCaps) (weightFloor := scE200CutWeightFloor) (margins := scE200CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE200Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE200Cut_layer0)
    (by decide +kernel) scE200Cut_caps_nonneg scE200Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE201CutCell) (roots := scE201CutRoots)
    (caps := scE201CutCaps) (weightFloor := scE201CutWeightFloor) (margins := scE201CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE201Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE201Cut_layer0)
    (by decide +kernel) scE201Cut_caps_nonneg scE201Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE202CutCell) (roots := scE202CutRoots)
    (caps := scE202CutCaps) (weightFloor := scE202CutWeightFloor) (margins := scE202CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE202Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE202Cut_layer0)
    (by decide +kernel) scE202Cut_caps_nonneg scE202Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := scE203CutCell) (roots := scE203CutRoots)
    (caps := scE203CutCaps) (weightFloor := scE203CutWeightFloor) (margins := scE203CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    scE203Cut_roots_ok (by
      intro i
      fin_cases i
      · exact scE203Cut_layer0)
    (by decide +kernel) scE203Cut_caps_nonneg scE203Cut_margin_le (by decide) (by decide +kernel)]

def scCutCurvatureCertificates : List (CurvatureCellCertificate) :=
  scCutCurvatureCertificates000 ++
  scCutCurvatureCertificates032 ++
  scCutCurvatureCertificates064 ++
  scCutCurvatureCertificates096 ++
  scCutCurvatureCertificates128 ++
  scCutCurvatureCertificates160 ++
  scCutCurvatureCertificates192 ++
  scCutCurvatureCertificates224 ++
  scCutCurvatureCertificates256 ++
  scCutCurvatureCertificates288 ++
  scCutCurvatureCertificates320 ++
  scCutCurvatureCertificates352 ++
  scCutCurvatureCertificates384 ++
  scCutCurvatureCertificates416 ++
  scCutCurvatureCertificates448 ++
  scCutCurvatureCertificates480

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem scCutCurvatureCertificates_cells :
    scCutCurvatureCertificates.map CurvatureCellCertificate.cell = scParameterGrid := by
  decide +kernel

end HlawkaSchatten.BelowExponent.Vertex
