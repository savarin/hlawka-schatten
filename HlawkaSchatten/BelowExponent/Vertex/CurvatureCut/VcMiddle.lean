/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCertificates
public import HlawkaSchatten.BelowExponent.Vertex.VcParameterGrid
meta import Mathlib.Tactic.FinCases
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks000
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks001
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks002
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks003
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks004
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks005
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks006
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks007
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks008
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks009
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks010
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks011
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks012
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks013
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks014
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcMiddleChecks015
public import HlawkaSchatten.BelowExponent.Vertex.CurvaturePilotVcM
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureData.VcM3
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcM58Pilot.Certificate
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureData.VcM60
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureData.VcM62
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureData.VcM63
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureData.VcM86
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureData.VcM87
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureData.VcM88
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureData.VcM89
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureData.VcM112
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureData.VcM113

/-! Checked curvature and weights on the same closed parameter grid. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcCutMiddleCertificates000 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcM0Cell) (roots := vcM0Roots)
    (caps := vcM0Caps) (weightFloor := vcM0WeightFloor) (margins := vcM0Margins)
    vcM0_roots_ok vcM0_grid_layers
    (by decide +kernel) vcM0_caps_nonneg vcM0_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM2CutCell) (roots := vcM2CutRoots)
    (caps := vcM2CutCaps) (weightFloor := vcM2CutWeightFloor) (margins := vcM2CutMargins)
    (na := 2) (nb := 2) (nη := 2)
    vcM2Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM2Cut_layer0
      · exact vcM2Cut_layer1)
    (by decide +kernel) vcM2Cut_caps_nonneg vcM2Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM3Cell) (roots := vcM3Roots)
    (caps := vcM3Caps) (weightFloor := vcM3WeightFloor) (margins := vcM3Margins)
    vcM3_roots_ok vcM3_grid_layers
    (by decide +kernel) vcM3_caps_nonneg vcM3_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM4CutCell) (roots := vcM4CutRoots)
    (caps := vcM4CutCaps) (weightFloor := vcM4CutWeightFloor) (margins := vcM4CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM4Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM4Cut_layer0)
    (by decide +kernel) vcM4Cut_caps_nonneg vcM4Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM5CutCell) (roots := vcM5CutRoots)
    (caps := vcM5CutCaps) (weightFloor := vcM5CutWeightFloor) (margins := vcM5CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM5Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM5Cut_layer0
      · exact vcM5Cut_layer1)
    (by decide +kernel) vcM5Cut_caps_nonneg vcM5Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM6CutCell) (roots := vcM6CutRoots)
    (caps := vcM6CutCaps) (weightFloor := vcM6CutWeightFloor) (margins := vcM6CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM6Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM6Cut_layer0)
    (by decide +kernel) vcM6Cut_caps_nonneg vcM6Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM7CutCell) (roots := vcM7CutRoots)
    (caps := vcM7CutCaps) (weightFloor := vcM7CutWeightFloor) (margins := vcM7CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM7Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM7Cut_layer0)
    (by decide +kernel) vcM7Cut_caps_nonneg vcM7Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM8CutCell) (roots := vcM8CutRoots)
    (caps := vcM8CutCaps) (weightFloor := vcM8CutWeightFloor) (margins := vcM8CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM8Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM8Cut_layer0)
    (by decide +kernel) vcM8Cut_caps_nonneg vcM8Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM9CutCell) (roots := vcM9CutRoots)
    (caps := vcM9CutCaps) (weightFloor := vcM9CutWeightFloor) (margins := vcM9CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM9Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM9Cut_layer0)
    (by decide +kernel) vcM9Cut_caps_nonneg vcM9Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM10CutCell) (roots := vcM10CutRoots)
    (caps := vcM10CutCaps) (weightFloor := vcM10CutWeightFloor) (margins := vcM10CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM10Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM10Cut_layer0)
    (by decide +kernel) vcM10Cut_caps_nonneg vcM10Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM11CutCell) (roots := vcM11CutRoots)
    (caps := vcM11CutCaps) (weightFloor := vcM11CutWeightFloor) (margins := vcM11CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM11Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM11Cut_layer0)
    (by decide +kernel) vcM11Cut_caps_nonneg vcM11Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM12CutCell) (roots := vcM12CutRoots)
    (caps := vcM12CutCaps) (weightFloor := vcM12CutWeightFloor) (margins := vcM12CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM12Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM12Cut_layer0)
    (by decide +kernel) vcM12Cut_caps_nonneg vcM12Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM13CutCell) (roots := vcM13CutRoots)
    (caps := vcM13CutCaps) (weightFloor := vcM13CutWeightFloor) (margins := vcM13CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM13Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM13Cut_layer0)
    (by decide +kernel) vcM13Cut_caps_nonneg vcM13Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM14CutCell) (roots := vcM14CutRoots)
    (caps := vcM14CutCaps) (weightFloor := vcM14CutWeightFloor) (margins := vcM14CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM14Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM14Cut_layer0)
    (by decide +kernel) vcM14Cut_caps_nonneg vcM14Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM15CutCell) (roots := vcM15CutRoots)
    (caps := vcM15CutCaps) (weightFloor := vcM15CutWeightFloor) (margins := vcM15CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM15Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM15Cut_layer0)
    (by decide +kernel) vcM15Cut_caps_nonneg vcM15Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM16CutCell) (roots := vcM16CutRoots)
    (caps := vcM16CutCaps) (weightFloor := vcM16CutWeightFloor) (margins := vcM16CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM16Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM16Cut_layer0)
    (by decide +kernel) vcM16Cut_caps_nonneg vcM16Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM17CutCell) (roots := vcM17CutRoots)
    (caps := vcM17CutCaps) (weightFloor := vcM17CutWeightFloor) (margins := vcM17CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM17Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM17Cut_layer0)
    (by decide +kernel) vcM17Cut_caps_nonneg vcM17Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM18CutCell) (roots := vcM18CutRoots)
    (caps := vcM18CutCaps) (weightFloor := vcM18CutWeightFloor) (margins := vcM18CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM18Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM18Cut_layer0)
    (by decide +kernel) vcM18Cut_caps_nonneg vcM18Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM19CutCell) (roots := vcM19CutRoots)
    (caps := vcM19CutCaps) (weightFloor := vcM19CutWeightFloor) (margins := vcM19CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM19Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM19Cut_layer0)
    (by decide +kernel) vcM19Cut_caps_nonneg vcM19Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM20CutCell) (roots := vcM20CutRoots)
    (caps := vcM20CutCaps) (weightFloor := vcM20CutWeightFloor) (margins := vcM20CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM20Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM20Cut_layer0)
    (by decide +kernel) vcM20Cut_caps_nonneg vcM20Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM21CutCell) (roots := vcM21CutRoots)
    (caps := vcM21CutCaps) (weightFloor := vcM21CutWeightFloor) (margins := vcM21CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM21Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM21Cut_layer0)
    (by decide +kernel) vcM21Cut_caps_nonneg vcM21Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM22CutCell) (roots := vcM22CutRoots)
    (caps := vcM22CutCaps) (weightFloor := vcM22CutWeightFloor) (margins := vcM22CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM22Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM22Cut_layer0)
    (by decide +kernel) vcM22Cut_caps_nonneg vcM22Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM23CutCell) (roots := vcM23CutRoots)
    (caps := vcM23CutCaps) (weightFloor := vcM23CutWeightFloor) (margins := vcM23CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM23Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM23Cut_layer0)
    (by decide +kernel) vcM23Cut_caps_nonneg vcM23Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM24CutCell) (roots := vcM24CutRoots)
    (caps := vcM24CutCaps) (weightFloor := vcM24CutWeightFloor) (margins := vcM24CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM24Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM24Cut_layer0)
    (by decide +kernel) vcM24Cut_caps_nonneg vcM24Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM25CutCell) (roots := vcM25CutRoots)
    (caps := vcM25CutCaps) (weightFloor := vcM25CutWeightFloor) (margins := vcM25CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM25Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM25Cut_layer0)
    (by decide +kernel) vcM25Cut_caps_nonneg vcM25Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM26CutCell) (roots := vcM26CutRoots)
    (caps := vcM26CutCaps) (weightFloor := vcM26CutWeightFloor) (margins := vcM26CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM26Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM26Cut_layer0)
    (by decide +kernel) vcM26Cut_caps_nonneg vcM26Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM27CutCell) (roots := vcM27CutRoots)
    (caps := vcM27CutCaps) (weightFloor := vcM27CutWeightFloor) (margins := vcM27CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM27Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM27Cut_layer0)
    (by decide +kernel) vcM27Cut_caps_nonneg vcM27Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM30CutCell) (roots := vcM30CutRoots)
    (caps := vcM30CutCaps) (weightFloor := vcM30CutWeightFloor) (margins := vcM30CutMargins)
    (na := 8) (nb := 8) (nη := 2)
    vcM30Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM30Cut_layer0
      · exact vcM30Cut_layer1
      · exact vcM30Cut_layer2
      · exact vcM30Cut_layer3
      · exact vcM30Cut_layer4
      · exact vcM30Cut_layer5
      · exact vcM30Cut_layer6
      · exact vcM30Cut_layer7)
    (by decide +kernel) vcM30Cut_caps_nonneg vcM30Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM32CutCell) (roots := vcM32CutRoots)
    (caps := vcM32CutCaps) (weightFloor := vcM32CutWeightFloor) (margins := vcM32CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM32Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM32Cut_layer0
      · exact vcM32Cut_layer1)
    (by decide +kernel) vcM32Cut_caps_nonneg vcM32Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM33CutCell) (roots := vcM33CutRoots)
    (caps := vcM33CutCaps) (weightFloor := vcM33CutWeightFloor) (margins := vcM33CutMargins)
    (na := 4) (nb := 4) (nη := 2)
    vcM33Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM33Cut_layer0
      · exact vcM33Cut_layer1
      · exact vcM33Cut_layer2
      · exact vcM33Cut_layer3)
    (by decide +kernel) vcM33Cut_caps_nonneg vcM33Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM34CutCell) (roots := vcM34CutRoots)
    (caps := vcM34CutCaps) (weightFloor := vcM34CutWeightFloor) (margins := vcM34CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM34Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM34Cut_layer0)
    (by decide +kernel) vcM34Cut_caps_nonneg vcM34Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM35CutCell) (roots := vcM35CutRoots)
    (caps := vcM35CutCaps) (weightFloor := vcM35CutWeightFloor) (margins := vcM35CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM35Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM35Cut_layer0
      · exact vcM35Cut_layer1)
    (by decide +kernel) vcM35Cut_caps_nonneg vcM35Cut_margin_le (by decide) (by decide +kernel)]

def vcCutMiddleCertificates032 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcM36CutCell) (roots := vcM36CutRoots)
    (caps := vcM36CutCaps) (weightFloor := vcM36CutWeightFloor) (margins := vcM36CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM36Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM36Cut_layer0)
    (by decide +kernel) vcM36Cut_caps_nonneg vcM36Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM37CutCell) (roots := vcM37CutRoots)
    (caps := vcM37CutCaps) (weightFloor := vcM37CutWeightFloor) (margins := vcM37CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM37Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM37Cut_layer0)
    (by decide +kernel) vcM37Cut_caps_nonneg vcM37Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM38CutCell) (roots := vcM38CutRoots)
    (caps := vcM38CutCaps) (weightFloor := vcM38CutWeightFloor) (margins := vcM38CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM38Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM38Cut_layer0)
    (by decide +kernel) vcM38Cut_caps_nonneg vcM38Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM39CutCell) (roots := vcM39CutRoots)
    (caps := vcM39CutCaps) (weightFloor := vcM39CutWeightFloor) (margins := vcM39CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM39Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM39Cut_layer0)
    (by decide +kernel) vcM39Cut_caps_nonneg vcM39Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM40CutCell) (roots := vcM40CutRoots)
    (caps := vcM40CutCaps) (weightFloor := vcM40CutWeightFloor) (margins := vcM40CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM40Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM40Cut_layer0)
    (by decide +kernel) vcM40Cut_caps_nonneg vcM40Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM41CutCell) (roots := vcM41CutRoots)
    (caps := vcM41CutCaps) (weightFloor := vcM41CutWeightFloor) (margins := vcM41CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM41Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM41Cut_layer0)
    (by decide +kernel) vcM41Cut_caps_nonneg vcM41Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM42CutCell) (roots := vcM42CutRoots)
    (caps := vcM42CutCaps) (weightFloor := vcM42CutWeightFloor) (margins := vcM42CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM42Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM42Cut_layer0)
    (by decide +kernel) vcM42Cut_caps_nonneg vcM42Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM43CutCell) (roots := vcM43CutRoots)
    (caps := vcM43CutCaps) (weightFloor := vcM43CutWeightFloor) (margins := vcM43CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM43Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM43Cut_layer0)
    (by decide +kernel) vcM43Cut_caps_nonneg vcM43Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM44CutCell) (roots := vcM44CutRoots)
    (caps := vcM44CutCaps) (weightFloor := vcM44CutWeightFloor) (margins := vcM44CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM44Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM44Cut_layer0)
    (by decide +kernel) vcM44Cut_caps_nonneg vcM44Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM45CutCell) (roots := vcM45CutRoots)
    (caps := vcM45CutCaps) (weightFloor := vcM45CutWeightFloor) (margins := vcM45CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM45Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM45Cut_layer0)
    (by decide +kernel) vcM45Cut_caps_nonneg vcM45Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM46CutCell) (roots := vcM46CutRoots)
    (caps := vcM46CutCaps) (weightFloor := vcM46CutWeightFloor) (margins := vcM46CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM46Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM46Cut_layer0)
    (by decide +kernel) vcM46Cut_caps_nonneg vcM46Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM47CutCell) (roots := vcM47CutRoots)
    (caps := vcM47CutCaps) (weightFloor := vcM47CutWeightFloor) (margins := vcM47CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM47Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM47Cut_layer0)
    (by decide +kernel) vcM47Cut_caps_nonneg vcM47Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM48CutCell) (roots := vcM48CutRoots)
    (caps := vcM48CutCaps) (weightFloor := vcM48CutWeightFloor) (margins := vcM48CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM48Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM48Cut_layer0)
    (by decide +kernel) vcM48Cut_caps_nonneg vcM48Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM49CutCell) (roots := vcM49CutRoots)
    (caps := vcM49CutCaps) (weightFloor := vcM49CutWeightFloor) (margins := vcM49CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM49Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM49Cut_layer0)
    (by decide +kernel) vcM49Cut_caps_nonneg vcM49Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM50CutCell) (roots := vcM50CutRoots)
    (caps := vcM50CutCaps) (weightFloor := vcM50CutWeightFloor) (margins := vcM50CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM50Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM50Cut_layer0)
    (by decide +kernel) vcM50Cut_caps_nonneg vcM50Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM51CutCell) (roots := vcM51CutRoots)
    (caps := vcM51CutCaps) (weightFloor := vcM51CutWeightFloor) (margins := vcM51CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM51Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM51Cut_layer0)
    (by decide +kernel) vcM51Cut_caps_nonneg vcM51Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM52CutCell) (roots := vcM52CutRoots)
    (caps := vcM52CutCaps) (weightFloor := vcM52CutWeightFloor) (margins := vcM52CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM52Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM52Cut_layer0)
    (by decide +kernel) vcM52Cut_caps_nonneg vcM52Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM53CutCell) (roots := vcM53CutRoots)
    (caps := vcM53CutCaps) (weightFloor := vcM53CutWeightFloor) (margins := vcM53CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM53Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM53Cut_layer0)
    (by decide +kernel) vcM53Cut_caps_nonneg vcM53Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM54CutCell) (roots := vcM54CutRoots)
    (caps := vcM54CutCaps) (weightFloor := vcM54CutWeightFloor) (margins := vcM54CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM54Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM54Cut_layer0)
    (by decide +kernel) vcM54Cut_caps_nonneg vcM54Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM55CutCell) (roots := vcM55CutRoots)
    (caps := vcM55CutCaps) (weightFloor := vcM55CutWeightFloor) (margins := vcM55CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM55Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM55Cut_layer0)
    (by decide +kernel) vcM55Cut_caps_nonneg vcM55Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM56CutCell) (roots := vcM56CutRoots)
    (caps := vcM56CutCaps) (weightFloor := vcM56CutWeightFloor) (margins := vcM56CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM56Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM56Cut_layer0)
    (by decide +kernel) vcM56Cut_caps_nonneg vcM56Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM57CutCell) (roots := vcM57CutRoots)
    (caps := vcM57CutCaps) (weightFloor := vcM57CutWeightFloor) (margins := vcM57CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM57Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM57Cut_layer0)
    (by decide +kernel) vcM57Cut_caps_nonneg vcM57Cut_margin_le (by decide) (by decide +kernel),
  vcM58PilotCertificate,
  CurvatureCellCertificate.of_layer_checks (c := vcM60Cell) (roots := vcM60Roots)
    (caps := vcM60Caps) (weightFloor := vcM60WeightFloor) (margins := vcM60Margins)
    vcM60_roots_ok vcM60_grid_layers
    (by decide +kernel) vcM60_caps_nonneg vcM60_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM62Cell) (roots := vcM62Roots)
    (caps := vcM62Caps) (weightFloor := vcM62WeightFloor) (margins := vcM62Margins)
    vcM62_roots_ok vcM62_grid_layers
    (by decide +kernel) vcM62_caps_nonneg vcM62_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM63Cell) (roots := vcM63Roots)
    (caps := vcM63Caps) (weightFloor := vcM63WeightFloor) (margins := vcM63Margins)
    vcM63_roots_ok vcM63_grid_layers
    (by decide +kernel) vcM63_caps_nonneg vcM63_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM64CutCell) (roots := vcM64CutRoots)
    (caps := vcM64CutCaps) (weightFloor := vcM64CutWeightFloor) (margins := vcM64CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM64Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM64Cut_layer0
      · exact vcM64Cut_layer1)
    (by decide +kernel) vcM64Cut_caps_nonneg vcM64Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM65CutCell) (roots := vcM65CutRoots)
    (caps := vcM65CutCaps) (weightFloor := vcM65CutWeightFloor) (margins := vcM65CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM65Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM65Cut_layer0
      · exact vcM65Cut_layer1)
    (by decide +kernel) vcM65Cut_caps_nonneg vcM65Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM66CutCell) (roots := vcM66CutRoots)
    (caps := vcM66CutCaps) (weightFloor := vcM66CutWeightFloor) (margins := vcM66CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM66Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM66Cut_layer0)
    (by decide +kernel) vcM66Cut_caps_nonneg vcM66Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM67CutCell) (roots := vcM67CutRoots)
    (caps := vcM67CutCaps) (weightFloor := vcM67CutWeightFloor) (margins := vcM67CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM67Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM67Cut_layer0)
    (by decide +kernel) vcM67Cut_caps_nonneg vcM67Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM68CutCell) (roots := vcM68CutRoots)
    (caps := vcM68CutCaps) (weightFloor := vcM68CutWeightFloor) (margins := vcM68CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM68Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM68Cut_layer0)
    (by decide +kernel) vcM68Cut_caps_nonneg vcM68Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM69CutCell) (roots := vcM69CutRoots)
    (caps := vcM69CutCaps) (weightFloor := vcM69CutWeightFloor) (margins := vcM69CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM69Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM69Cut_layer0)
    (by decide +kernel) vcM69Cut_caps_nonneg vcM69Cut_margin_le (by decide) (by decide +kernel)]

def vcCutMiddleCertificates064 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcM70CutCell) (roots := vcM70CutRoots)
    (caps := vcM70CutCaps) (weightFloor := vcM70CutWeightFloor) (margins := vcM70CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM70Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM70Cut_layer0)
    (by decide +kernel) vcM70Cut_caps_nonneg vcM70Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM71CutCell) (roots := vcM71CutRoots)
    (caps := vcM71CutCaps) (weightFloor := vcM71CutWeightFloor) (margins := vcM71CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM71Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM71Cut_layer0)
    (by decide +kernel) vcM71Cut_caps_nonneg vcM71Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM72CutCell) (roots := vcM72CutRoots)
    (caps := vcM72CutCaps) (weightFloor := vcM72CutWeightFloor) (margins := vcM72CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM72Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM72Cut_layer0)
    (by decide +kernel) vcM72Cut_caps_nonneg vcM72Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM73CutCell) (roots := vcM73CutRoots)
    (caps := vcM73CutCaps) (weightFloor := vcM73CutWeightFloor) (margins := vcM73CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM73Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM73Cut_layer0)
    (by decide +kernel) vcM73Cut_caps_nonneg vcM73Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM74CutCell) (roots := vcM74CutRoots)
    (caps := vcM74CutCaps) (weightFloor := vcM74CutWeightFloor) (margins := vcM74CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM74Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM74Cut_layer0)
    (by decide +kernel) vcM74Cut_caps_nonneg vcM74Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM75CutCell) (roots := vcM75CutRoots)
    (caps := vcM75CutCaps) (weightFloor := vcM75CutWeightFloor) (margins := vcM75CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM75Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM75Cut_layer0)
    (by decide +kernel) vcM75Cut_caps_nonneg vcM75Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM76CutCell) (roots := vcM76CutRoots)
    (caps := vcM76CutCaps) (weightFloor := vcM76CutWeightFloor) (margins := vcM76CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM76Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM76Cut_layer0)
    (by decide +kernel) vcM76Cut_caps_nonneg vcM76Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM77CutCell) (roots := vcM77CutRoots)
    (caps := vcM77CutCaps) (weightFloor := vcM77CutWeightFloor) (margins := vcM77CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM77Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM77Cut_layer0)
    (by decide +kernel) vcM77Cut_caps_nonneg vcM77Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM78CutCell) (roots := vcM78CutRoots)
    (caps := vcM78CutCaps) (weightFloor := vcM78CutWeightFloor) (margins := vcM78CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM78Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM78Cut_layer0)
    (by decide +kernel) vcM78Cut_caps_nonneg vcM78Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM79CutCell) (roots := vcM79CutRoots)
    (caps := vcM79CutCaps) (weightFloor := vcM79CutWeightFloor) (margins := vcM79CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM79Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM79Cut_layer0)
    (by decide +kernel) vcM79Cut_caps_nonneg vcM79Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM80CutCell) (roots := vcM80CutRoots)
    (caps := vcM80CutCaps) (weightFloor := vcM80CutWeightFloor) (margins := vcM80CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM80Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM80Cut_layer0)
    (by decide +kernel) vcM80Cut_caps_nonneg vcM80Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM81CutCell) (roots := vcM81CutRoots)
    (caps := vcM81CutCaps) (weightFloor := vcM81CutWeightFloor) (margins := vcM81CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM81Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM81Cut_layer0)
    (by decide +kernel) vcM81Cut_caps_nonneg vcM81Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM82CutCell) (roots := vcM82CutRoots)
    (caps := vcM82CutCaps) (weightFloor := vcM82CutWeightFloor) (margins := vcM82CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM82Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM82Cut_layer0)
    (by decide +kernel) vcM82Cut_caps_nonneg vcM82Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM83CutCell) (roots := vcM83CutRoots)
    (caps := vcM83CutCaps) (weightFloor := vcM83CutWeightFloor) (margins := vcM83CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM83Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM83Cut_layer0)
    (by decide +kernel) vcM83Cut_caps_nonneg vcM83Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM84CutCell) (roots := vcM84CutRoots)
    (caps := vcM84CutCaps) (weightFloor := vcM84CutWeightFloor) (margins := vcM84CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM84Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM84Cut_layer0)
    (by decide +kernel) vcM84Cut_caps_nonneg vcM84Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM85CutCell) (roots := vcM85CutRoots)
    (caps := vcM85CutCaps) (weightFloor := vcM85CutWeightFloor) (margins := vcM85CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM85Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM85Cut_layer0)
    (by decide +kernel) vcM85Cut_caps_nonneg vcM85Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM86Cell) (roots := vcM86Roots)
    (caps := vcM86Caps) (weightFloor := vcM86WeightFloor) (margins := vcM86Margins)
    vcM86_roots_ok vcM86_grid_layers
    (by decide +kernel) vcM86_caps_nonneg vcM86_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM87Cell) (roots := vcM87Roots)
    (caps := vcM87Caps) (weightFloor := vcM87WeightFloor) (margins := vcM87Margins)
    vcM87_roots_ok vcM87_grid_layers
    (by decide +kernel) vcM87_caps_nonneg vcM87_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM88Cell) (roots := vcM88Roots)
    (caps := vcM88Caps) (weightFloor := vcM88WeightFloor) (margins := vcM88Margins)
    vcM88_roots_ok vcM88_grid_layers
    (by decide +kernel) vcM88_caps_nonneg vcM88_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM89Cell) (roots := vcM89Roots)
    (caps := vcM89Caps) (weightFloor := vcM89WeightFloor) (margins := vcM89Margins)
    vcM89_roots_ok vcM89_grid_layers
    (by decide +kernel) vcM89_caps_nonneg vcM89_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM90CutCell) (roots := vcM90CutRoots)
    (caps := vcM90CutCaps) (weightFloor := vcM90CutWeightFloor) (margins := vcM90CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM90Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM90Cut_layer0
      · exact vcM90Cut_layer1)
    (by decide +kernel) vcM90Cut_caps_nonneg vcM90Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM91CutCell) (roots := vcM91CutRoots)
    (caps := vcM91CutCaps) (weightFloor := vcM91CutWeightFloor) (margins := vcM91CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM91Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM91Cut_layer0
      · exact vcM91Cut_layer1)
    (by decide +kernel) vcM91Cut_caps_nonneg vcM91Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM92CutCell) (roots := vcM92CutRoots)
    (caps := vcM92CutCaps) (weightFloor := vcM92CutWeightFloor) (margins := vcM92CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM92Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM92Cut_layer0)
    (by decide +kernel) vcM92Cut_caps_nonneg vcM92Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM93CutCell) (roots := vcM93CutRoots)
    (caps := vcM93CutCaps) (weightFloor := vcM93CutWeightFloor) (margins := vcM93CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM93Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM93Cut_layer0)
    (by decide +kernel) vcM93Cut_caps_nonneg vcM93Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM94CutCell) (roots := vcM94CutRoots)
    (caps := vcM94CutCaps) (weightFloor := vcM94CutWeightFloor) (margins := vcM94CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM94Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM94Cut_layer0)
    (by decide +kernel) vcM94Cut_caps_nonneg vcM94Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM95CutCell) (roots := vcM95CutRoots)
    (caps := vcM95CutCaps) (weightFloor := vcM95CutWeightFloor) (margins := vcM95CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM95Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM95Cut_layer0)
    (by decide +kernel) vcM95Cut_caps_nonneg vcM95Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM96CutCell) (roots := vcM96CutRoots)
    (caps := vcM96CutCaps) (weightFloor := vcM96CutWeightFloor) (margins := vcM96CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM96Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM96Cut_layer0)
    (by decide +kernel) vcM96Cut_caps_nonneg vcM96Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM97CutCell) (roots := vcM97CutRoots)
    (caps := vcM97CutCaps) (weightFloor := vcM97CutWeightFloor) (margins := vcM97CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM97Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM97Cut_layer0)
    (by decide +kernel) vcM97Cut_caps_nonneg vcM97Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM98CutCell) (roots := vcM98CutRoots)
    (caps := vcM98CutCaps) (weightFloor := vcM98CutWeightFloor) (margins := vcM98CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM98Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM98Cut_layer0)
    (by decide +kernel) vcM98Cut_caps_nonneg vcM98Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM99CutCell) (roots := vcM99CutRoots)
    (caps := vcM99CutCaps) (weightFloor := vcM99CutWeightFloor) (margins := vcM99CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM99Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM99Cut_layer0)
    (by decide +kernel) vcM99Cut_caps_nonneg vcM99Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM100CutCell) (roots := vcM100CutRoots)
    (caps := vcM100CutCaps) (weightFloor := vcM100CutWeightFloor) (margins := vcM100CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM100Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM100Cut_layer0)
    (by decide +kernel) vcM100Cut_caps_nonneg vcM100Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM101CutCell) (roots := vcM101CutRoots)
    (caps := vcM101CutCaps) (weightFloor := vcM101CutWeightFloor) (margins := vcM101CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM101Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM101Cut_layer0)
    (by decide +kernel) vcM101Cut_caps_nonneg vcM101Cut_margin_le (by decide) (by decide +kernel)]

def vcCutMiddleCertificates096 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcM102CutCell) (roots := vcM102CutRoots)
    (caps := vcM102CutCaps) (weightFloor := vcM102CutWeightFloor) (margins := vcM102CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM102Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM102Cut_layer0)
    (by decide +kernel) vcM102Cut_caps_nonneg vcM102Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM103CutCell) (roots := vcM103CutRoots)
    (caps := vcM103CutCaps) (weightFloor := vcM103CutWeightFloor) (margins := vcM103CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM103Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM103Cut_layer0)
    (by decide +kernel) vcM103Cut_caps_nonneg vcM103Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM104CutCell) (roots := vcM104CutRoots)
    (caps := vcM104CutCaps) (weightFloor := vcM104CutWeightFloor) (margins := vcM104CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM104Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM104Cut_layer0)
    (by decide +kernel) vcM104Cut_caps_nonneg vcM104Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM105CutCell) (roots := vcM105CutRoots)
    (caps := vcM105CutCaps) (weightFloor := vcM105CutWeightFloor) (margins := vcM105CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM105Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM105Cut_layer0)
    (by decide +kernel) vcM105Cut_caps_nonneg vcM105Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM106CutCell) (roots := vcM106CutRoots)
    (caps := vcM106CutCaps) (weightFloor := vcM106CutWeightFloor) (margins := vcM106CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM106Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM106Cut_layer0)
    (by decide +kernel) vcM106Cut_caps_nonneg vcM106Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM107CutCell) (roots := vcM107CutRoots)
    (caps := vcM107CutCaps) (weightFloor := vcM107CutWeightFloor) (margins := vcM107CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM107Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM107Cut_layer0)
    (by decide +kernel) vcM107Cut_caps_nonneg vcM107Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM108CutCell) (roots := vcM108CutRoots)
    (caps := vcM108CutCaps) (weightFloor := vcM108CutWeightFloor) (margins := vcM108CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM108Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM108Cut_layer0)
    (by decide +kernel) vcM108Cut_caps_nonneg vcM108Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM109CutCell) (roots := vcM109CutRoots)
    (caps := vcM109CutCaps) (weightFloor := vcM109CutWeightFloor) (margins := vcM109CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM109Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM109Cut_layer0)
    (by decide +kernel) vcM109Cut_caps_nonneg vcM109Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM110CutCell) (roots := vcM110CutRoots)
    (caps := vcM110CutCaps) (weightFloor := vcM110CutWeightFloor) (margins := vcM110CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM110Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM110Cut_layer0)
    (by decide +kernel) vcM110Cut_caps_nonneg vcM110Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM111CutCell) (roots := vcM111CutRoots)
    (caps := vcM111CutCaps) (weightFloor := vcM111CutWeightFloor) (margins := vcM111CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM111Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM111Cut_layer0)
    (by decide +kernel) vcM111Cut_caps_nonneg vcM111Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM112Cell) (roots := vcM112Roots)
    (caps := vcM112Caps) (weightFloor := vcM112WeightFloor) (margins := vcM112Margins)
    vcM112_roots_ok vcM112_grid_layers
    (by decide +kernel) vcM112_caps_nonneg vcM112_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM113Cell) (roots := vcM113Roots)
    (caps := vcM113Caps) (weightFloor := vcM113WeightFloor) (margins := vcM113Margins)
    vcM113_roots_ok vcM113_grid_layers
    (by decide +kernel) vcM113_caps_nonneg vcM113_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM114CutCell) (roots := vcM114CutRoots)
    (caps := vcM114CutCaps) (weightFloor := vcM114CutWeightFloor) (margins := vcM114CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM114Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM114Cut_layer0
      · exact vcM114Cut_layer1)
    (by decide +kernel) vcM114Cut_caps_nonneg vcM114Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM115CutCell) (roots := vcM115CutRoots)
    (caps := vcM115CutCaps) (weightFloor := vcM115CutWeightFloor) (margins := vcM115CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM115Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM115Cut_layer0
      · exact vcM115Cut_layer1)
    (by decide +kernel) vcM115Cut_caps_nonneg vcM115Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM116CutCell) (roots := vcM116CutRoots)
    (caps := vcM116CutCaps) (weightFloor := vcM116CutWeightFloor) (margins := vcM116CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM116Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM116Cut_layer0)
    (by decide +kernel) vcM116Cut_caps_nonneg vcM116Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM117CutCell) (roots := vcM117CutRoots)
    (caps := vcM117CutCaps) (weightFloor := vcM117CutWeightFloor) (margins := vcM117CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM117Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM117Cut_layer0
      · exact vcM117Cut_layer1)
    (by decide +kernel) vcM117Cut_caps_nonneg vcM117Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM118CutCell) (roots := vcM118CutRoots)
    (caps := vcM118CutCaps) (weightFloor := vcM118CutWeightFloor) (margins := vcM118CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM118Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM118Cut_layer0)
    (by decide +kernel) vcM118Cut_caps_nonneg vcM118Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM119CutCell) (roots := vcM119CutRoots)
    (caps := vcM119CutCaps) (weightFloor := vcM119CutWeightFloor) (margins := vcM119CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM119Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM119Cut_layer0)
    (by decide +kernel) vcM119Cut_caps_nonneg vcM119Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM120CutCell) (roots := vcM120CutRoots)
    (caps := vcM120CutCaps) (weightFloor := vcM120CutWeightFloor) (margins := vcM120CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM120Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM120Cut_layer0)
    (by decide +kernel) vcM120Cut_caps_nonneg vcM120Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM121CutCell) (roots := vcM121CutRoots)
    (caps := vcM121CutCaps) (weightFloor := vcM121CutWeightFloor) (margins := vcM121CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM121Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM121Cut_layer0)
    (by decide +kernel) vcM121Cut_caps_nonneg vcM121Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM122CutCell) (roots := vcM122CutRoots)
    (caps := vcM122CutCaps) (weightFloor := vcM122CutWeightFloor) (margins := vcM122CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM122Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM122Cut_layer0)
    (by decide +kernel) vcM122Cut_caps_nonneg vcM122Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM123CutCell) (roots := vcM123CutRoots)
    (caps := vcM123CutCaps) (weightFloor := vcM123CutWeightFloor) (margins := vcM123CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM123Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM123Cut_layer0)
    (by decide +kernel) vcM123Cut_caps_nonneg vcM123Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM124CutCell) (roots := vcM124CutRoots)
    (caps := vcM124CutCaps) (weightFloor := vcM124CutWeightFloor) (margins := vcM124CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM124Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM124Cut_layer0)
    (by decide +kernel) vcM124Cut_caps_nonneg vcM124Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM125CutCell) (roots := vcM125CutRoots)
    (caps := vcM125CutCaps) (weightFloor := vcM125CutWeightFloor) (margins := vcM125CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM125Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM125Cut_layer0)
    (by decide +kernel) vcM125Cut_caps_nonneg vcM125Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM126CutCell) (roots := vcM126CutRoots)
    (caps := vcM126CutCaps) (weightFloor := vcM126CutWeightFloor) (margins := vcM126CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM126Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM126Cut_layer0)
    (by decide +kernel) vcM126Cut_caps_nonneg vcM126Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM127CutCell) (roots := vcM127CutRoots)
    (caps := vcM127CutCaps) (weightFloor := vcM127CutWeightFloor) (margins := vcM127CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM127Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM127Cut_layer0)
    (by decide +kernel) vcM127Cut_caps_nonneg vcM127Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM128CutCell) (roots := vcM128CutRoots)
    (caps := vcM128CutCaps) (weightFloor := vcM128CutWeightFloor) (margins := vcM128CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM128Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM128Cut_layer0)
    (by decide +kernel) vcM128Cut_caps_nonneg vcM128Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM129CutCell) (roots := vcM129CutRoots)
    (caps := vcM129CutCaps) (weightFloor := vcM129CutWeightFloor) (margins := vcM129CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM129Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM129Cut_layer0)
    (by decide +kernel) vcM129Cut_caps_nonneg vcM129Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM130CutCell) (roots := vcM130CutRoots)
    (caps := vcM130CutCaps) (weightFloor := vcM130CutWeightFloor) (margins := vcM130CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM130Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM130Cut_layer0)
    (by decide +kernel) vcM130Cut_caps_nonneg vcM130Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM131CutCell) (roots := vcM131CutRoots)
    (caps := vcM131CutCaps) (weightFloor := vcM131CutWeightFloor) (margins := vcM131CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM131Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM131Cut_layer0)
    (by decide +kernel) vcM131Cut_caps_nonneg vcM131Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM132CutCell) (roots := vcM132CutRoots)
    (caps := vcM132CutCaps) (weightFloor := vcM132CutWeightFloor) (margins := vcM132CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM132Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM132Cut_layer0)
    (by decide +kernel) vcM132Cut_caps_nonneg vcM132Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM133CutCell) (roots := vcM133CutRoots)
    (caps := vcM133CutCaps) (weightFloor := vcM133CutWeightFloor) (margins := vcM133CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM133Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM133Cut_layer0)
    (by decide +kernel) vcM133Cut_caps_nonneg vcM133Cut_margin_le (by decide) (by decide +kernel)]

def vcCutMiddleCertificates128 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcM134CutCell) (roots := vcM134CutRoots)
    (caps := vcM134CutCaps) (weightFloor := vcM134CutWeightFloor) (margins := vcM134CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM134Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM134Cut_layer0
      · exact vcM134Cut_layer1)
    (by decide +kernel) vcM134Cut_caps_nonneg vcM134Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM135CutCell) (roots := vcM135CutRoots)
    (caps := vcM135CutCaps) (weightFloor := vcM135CutWeightFloor) (margins := vcM135CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM135Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM135Cut_layer0
      · exact vcM135Cut_layer1)
    (by decide +kernel) vcM135Cut_caps_nonneg vcM135Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM136CutCell) (roots := vcM136CutRoots)
    (caps := vcM136CutCaps) (weightFloor := vcM136CutWeightFloor) (margins := vcM136CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM136Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM136Cut_layer0)
    (by decide +kernel) vcM136Cut_caps_nonneg vcM136Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM137CutCell) (roots := vcM137CutRoots)
    (caps := vcM137CutCaps) (weightFloor := vcM137CutWeightFloor) (margins := vcM137CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM137Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM137Cut_layer0
      · exact vcM137Cut_layer1)
    (by decide +kernel) vcM137Cut_caps_nonneg vcM137Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM138CutCell) (roots := vcM138CutRoots)
    (caps := vcM138CutCaps) (weightFloor := vcM138CutWeightFloor) (margins := vcM138CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM138Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM138Cut_layer0)
    (by decide +kernel) vcM138Cut_caps_nonneg vcM138Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM139CutCell) (roots := vcM139CutRoots)
    (caps := vcM139CutCaps) (weightFloor := vcM139CutWeightFloor) (margins := vcM139CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM139Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM139Cut_layer0)
    (by decide +kernel) vcM139Cut_caps_nonneg vcM139Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM140CutCell) (roots := vcM140CutRoots)
    (caps := vcM140CutCaps) (weightFloor := vcM140CutWeightFloor) (margins := vcM140CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM140Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM140Cut_layer0)
    (by decide +kernel) vcM140Cut_caps_nonneg vcM140Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM141CutCell) (roots := vcM141CutRoots)
    (caps := vcM141CutCaps) (weightFloor := vcM141CutWeightFloor) (margins := vcM141CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM141Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM141Cut_layer0)
    (by decide +kernel) vcM141Cut_caps_nonneg vcM141Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM142CutCell) (roots := vcM142CutRoots)
    (caps := vcM142CutCaps) (weightFloor := vcM142CutWeightFloor) (margins := vcM142CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM142Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM142Cut_layer0)
    (by decide +kernel) vcM142Cut_caps_nonneg vcM142Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM143CutCell) (roots := vcM143CutRoots)
    (caps := vcM143CutCaps) (weightFloor := vcM143CutWeightFloor) (margins := vcM143CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM143Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM143Cut_layer0)
    (by decide +kernel) vcM143Cut_caps_nonneg vcM143Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM144CutCell) (roots := vcM144CutRoots)
    (caps := vcM144CutCaps) (weightFloor := vcM144CutWeightFloor) (margins := vcM144CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM144Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM144Cut_layer0)
    (by decide +kernel) vcM144Cut_caps_nonneg vcM144Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM145CutCell) (roots := vcM145CutRoots)
    (caps := vcM145CutCaps) (weightFloor := vcM145CutWeightFloor) (margins := vcM145CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM145Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM145Cut_layer0)
    (by decide +kernel) vcM145Cut_caps_nonneg vcM145Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM146CutCell) (roots := vcM146CutRoots)
    (caps := vcM146CutCaps) (weightFloor := vcM146CutWeightFloor) (margins := vcM146CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM146Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM146Cut_layer0)
    (by decide +kernel) vcM146Cut_caps_nonneg vcM146Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM147CutCell) (roots := vcM147CutRoots)
    (caps := vcM147CutCaps) (weightFloor := vcM147CutWeightFloor) (margins := vcM147CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM147Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM147Cut_layer0)
    (by decide +kernel) vcM147Cut_caps_nonneg vcM147Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM148CutCell) (roots := vcM148CutRoots)
    (caps := vcM148CutCaps) (weightFloor := vcM148CutWeightFloor) (margins := vcM148CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM148Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM148Cut_layer0)
    (by decide +kernel) vcM148Cut_caps_nonneg vcM148Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM149CutCell) (roots := vcM149CutRoots)
    (caps := vcM149CutCaps) (weightFloor := vcM149CutWeightFloor) (margins := vcM149CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM149Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM149Cut_layer0)
    (by decide +kernel) vcM149Cut_caps_nonneg vcM149Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM150CutCell) (roots := vcM150CutRoots)
    (caps := vcM150CutCaps) (weightFloor := vcM150CutWeightFloor) (margins := vcM150CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM150Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM150Cut_layer0)
    (by decide +kernel) vcM150Cut_caps_nonneg vcM150Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM151CutCell) (roots := vcM151CutRoots)
    (caps := vcM151CutCaps) (weightFloor := vcM151CutWeightFloor) (margins := vcM151CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM151Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM151Cut_layer0)
    (by decide +kernel) vcM151Cut_caps_nonneg vcM151Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM152CutCell) (roots := vcM152CutRoots)
    (caps := vcM152CutCaps) (weightFloor := vcM152CutWeightFloor) (margins := vcM152CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM152Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM152Cut_layer0)
    (by decide +kernel) vcM152Cut_caps_nonneg vcM152Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM153CutCell) (roots := vcM153CutRoots)
    (caps := vcM153CutCaps) (weightFloor := vcM153CutWeightFloor) (margins := vcM153CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM153Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM153Cut_layer0)
    (by decide +kernel) vcM153Cut_caps_nonneg vcM153Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM154CutCell) (roots := vcM154CutRoots)
    (caps := vcM154CutCaps) (weightFloor := vcM154CutWeightFloor) (margins := vcM154CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM154Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM154Cut_layer0)
    (by decide +kernel) vcM154Cut_caps_nonneg vcM154Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM155CutCell) (roots := vcM155CutRoots)
    (caps := vcM155CutCaps) (weightFloor := vcM155CutWeightFloor) (margins := vcM155CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM155Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM155Cut_layer0
      · exact vcM155Cut_layer1)
    (by decide +kernel) vcM155Cut_caps_nonneg vcM155Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM156CutCell) (roots := vcM156CutRoots)
    (caps := vcM156CutCaps) (weightFloor := vcM156CutWeightFloor) (margins := vcM156CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM156Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM156Cut_layer0)
    (by decide +kernel) vcM156Cut_caps_nonneg vcM156Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM157CutCell) (roots := vcM157CutRoots)
    (caps := vcM157CutCaps) (weightFloor := vcM157CutWeightFloor) (margins := vcM157CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM157Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM157Cut_layer0)
    (by decide +kernel) vcM157Cut_caps_nonneg vcM157Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM158CutCell) (roots := vcM158CutRoots)
    (caps := vcM158CutCaps) (weightFloor := vcM158CutWeightFloor) (margins := vcM158CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM158Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM158Cut_layer0)
    (by decide +kernel) vcM158Cut_caps_nonneg vcM158Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM159CutCell) (roots := vcM159CutRoots)
    (caps := vcM159CutCaps) (weightFloor := vcM159CutWeightFloor) (margins := vcM159CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM159Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM159Cut_layer0)
    (by decide +kernel) vcM159Cut_caps_nonneg vcM159Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM160CutCell) (roots := vcM160CutRoots)
    (caps := vcM160CutCaps) (weightFloor := vcM160CutWeightFloor) (margins := vcM160CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM160Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM160Cut_layer0)
    (by decide +kernel) vcM160Cut_caps_nonneg vcM160Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM161CutCell) (roots := vcM161CutRoots)
    (caps := vcM161CutCaps) (weightFloor := vcM161CutWeightFloor) (margins := vcM161CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM161Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM161Cut_layer0)
    (by decide +kernel) vcM161Cut_caps_nonneg vcM161Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM162CutCell) (roots := vcM162CutRoots)
    (caps := vcM162CutCaps) (weightFloor := vcM162CutWeightFloor) (margins := vcM162CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM162Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM162Cut_layer0)
    (by decide +kernel) vcM162Cut_caps_nonneg vcM162Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM163CutCell) (roots := vcM163CutRoots)
    (caps := vcM163CutCaps) (weightFloor := vcM163CutWeightFloor) (margins := vcM163CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM163Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM163Cut_layer0)
    (by decide +kernel) vcM163Cut_caps_nonneg vcM163Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM164CutCell) (roots := vcM164CutRoots)
    (caps := vcM164CutCaps) (weightFloor := vcM164CutWeightFloor) (margins := vcM164CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM164Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM164Cut_layer0)
    (by decide +kernel) vcM164Cut_caps_nonneg vcM164Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM165CutCell) (roots := vcM165CutRoots)
    (caps := vcM165CutCaps) (weightFloor := vcM165CutWeightFloor) (margins := vcM165CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM165Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM165Cut_layer0)
    (by decide +kernel) vcM165Cut_caps_nonneg vcM165Cut_margin_le (by decide) (by decide +kernel)]

def vcCutMiddleCertificates160 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcM166CutCell) (roots := vcM166CutRoots)
    (caps := vcM166CutCaps) (weightFloor := vcM166CutWeightFloor) (margins := vcM166CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM166Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM166Cut_layer0)
    (by decide +kernel) vcM166Cut_caps_nonneg vcM166Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM167CutCell) (roots := vcM167CutRoots)
    (caps := vcM167CutCaps) (weightFloor := vcM167CutWeightFloor) (margins := vcM167CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM167Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM167Cut_layer0)
    (by decide +kernel) vcM167Cut_caps_nonneg vcM167Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM168CutCell) (roots := vcM168CutRoots)
    (caps := vcM168CutCaps) (weightFloor := vcM168CutWeightFloor) (margins := vcM168CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM168Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM168Cut_layer0)
    (by decide +kernel) vcM168Cut_caps_nonneg vcM168Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM169CutCell) (roots := vcM169CutRoots)
    (caps := vcM169CutCaps) (weightFloor := vcM169CutWeightFloor) (margins := vcM169CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM169Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM169Cut_layer0)
    (by decide +kernel) vcM169Cut_caps_nonneg vcM169Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM170CutCell) (roots := vcM170CutRoots)
    (caps := vcM170CutCaps) (weightFloor := vcM170CutWeightFloor) (margins := vcM170CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM170Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM170Cut_layer0)
    (by decide +kernel) vcM170Cut_caps_nonneg vcM170Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM171CutCell) (roots := vcM171CutRoots)
    (caps := vcM171CutCaps) (weightFloor := vcM171CutWeightFloor) (margins := vcM171CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM171Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM171Cut_layer0)
    (by decide +kernel) vcM171Cut_caps_nonneg vcM171Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM172CutCell) (roots := vcM172CutRoots)
    (caps := vcM172CutCaps) (weightFloor := vcM172CutWeightFloor) (margins := vcM172CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM172Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM172Cut_layer0)
    (by decide +kernel) vcM172Cut_caps_nonneg vcM172Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM173CutCell) (roots := vcM173CutRoots)
    (caps := vcM173CutCaps) (weightFloor := vcM173CutWeightFloor) (margins := vcM173CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM173Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM173Cut_layer0)
    (by decide +kernel) vcM173Cut_caps_nonneg vcM173Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM174CutCell) (roots := vcM174CutRoots)
    (caps := vcM174CutCaps) (weightFloor := vcM174CutWeightFloor) (margins := vcM174CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM174Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM174Cut_layer0)
    (by decide +kernel) vcM174Cut_caps_nonneg vcM174Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM175CutCell) (roots := vcM175CutRoots)
    (caps := vcM175CutCaps) (weightFloor := vcM175CutWeightFloor) (margins := vcM175CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM175Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM175Cut_layer0)
    (by decide +kernel) vcM175Cut_caps_nonneg vcM175Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM176CutCell) (roots := vcM176CutRoots)
    (caps := vcM176CutCaps) (weightFloor := vcM176CutWeightFloor) (margins := vcM176CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM176Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM176Cut_layer0)
    (by decide +kernel) vcM176Cut_caps_nonneg vcM176Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM177CutCell) (roots := vcM177CutRoots)
    (caps := vcM177CutCaps) (weightFloor := vcM177CutWeightFloor) (margins := vcM177CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM177Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM177Cut_layer0)
    (by decide +kernel) vcM177Cut_caps_nonneg vcM177Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM178CutCell) (roots := vcM178CutRoots)
    (caps := vcM178CutCaps) (weightFloor := vcM178CutWeightFloor) (margins := vcM178CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM178Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM178Cut_layer0)
    (by decide +kernel) vcM178Cut_caps_nonneg vcM178Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM179CutCell) (roots := vcM179CutRoots)
    (caps := vcM179CutCaps) (weightFloor := vcM179CutWeightFloor) (margins := vcM179CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM179Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM179Cut_layer0)
    (by decide +kernel) vcM179Cut_caps_nonneg vcM179Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM180CutCell) (roots := vcM180CutRoots)
    (caps := vcM180CutCaps) (weightFloor := vcM180CutWeightFloor) (margins := vcM180CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM180Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM180Cut_layer0)
    (by decide +kernel) vcM180Cut_caps_nonneg vcM180Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM181CutCell) (roots := vcM181CutRoots)
    (caps := vcM181CutCaps) (weightFloor := vcM181CutWeightFloor) (margins := vcM181CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM181Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM181Cut_layer0)
    (by decide +kernel) vcM181Cut_caps_nonneg vcM181Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM182CutCell) (roots := vcM182CutRoots)
    (caps := vcM182CutCaps) (weightFloor := vcM182CutWeightFloor) (margins := vcM182CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM182Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM182Cut_layer0)
    (by decide +kernel) vcM182Cut_caps_nonneg vcM182Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM183CutCell) (roots := vcM183CutRoots)
    (caps := vcM183CutCaps) (weightFloor := vcM183CutWeightFloor) (margins := vcM183CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM183Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM183Cut_layer0)
    (by decide +kernel) vcM183Cut_caps_nonneg vcM183Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM184CutCell) (roots := vcM184CutRoots)
    (caps := vcM184CutCaps) (weightFloor := vcM184CutWeightFloor) (margins := vcM184CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM184Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM184Cut_layer0)
    (by decide +kernel) vcM184Cut_caps_nonneg vcM184Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM185CutCell) (roots := vcM185CutRoots)
    (caps := vcM185CutCaps) (weightFloor := vcM185CutWeightFloor) (margins := vcM185CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM185Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM185Cut_layer0)
    (by decide +kernel) vcM185Cut_caps_nonneg vcM185Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM186CutCell) (roots := vcM186CutRoots)
    (caps := vcM186CutCaps) (weightFloor := vcM186CutWeightFloor) (margins := vcM186CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM186Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM186Cut_layer0)
    (by decide +kernel) vcM186Cut_caps_nonneg vcM186Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM187CutCell) (roots := vcM187CutRoots)
    (caps := vcM187CutCaps) (weightFloor := vcM187CutWeightFloor) (margins := vcM187CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM187Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM187Cut_layer0)
    (by decide +kernel) vcM187Cut_caps_nonneg vcM187Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM188CutCell) (roots := vcM188CutRoots)
    (caps := vcM188CutCaps) (weightFloor := vcM188CutWeightFloor) (margins := vcM188CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM188Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM188Cut_layer0)
    (by decide +kernel) vcM188Cut_caps_nonneg vcM188Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM189CutCell) (roots := vcM189CutRoots)
    (caps := vcM189CutCaps) (weightFloor := vcM189CutWeightFloor) (margins := vcM189CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM189Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM189Cut_layer0)
    (by decide +kernel) vcM189Cut_caps_nonneg vcM189Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM190CutCell) (roots := vcM190CutRoots)
    (caps := vcM190CutCaps) (weightFloor := vcM190CutWeightFloor) (margins := vcM190CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM190Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM190Cut_layer0)
    (by decide +kernel) vcM190Cut_caps_nonneg vcM190Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM191CutCell) (roots := vcM191CutRoots)
    (caps := vcM191CutCaps) (weightFloor := vcM191CutWeightFloor) (margins := vcM191CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM191Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM191Cut_layer0)
    (by decide +kernel) vcM191Cut_caps_nonneg vcM191Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM192CutCell) (roots := vcM192CutRoots)
    (caps := vcM192CutCaps) (weightFloor := vcM192CutWeightFloor) (margins := vcM192CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM192Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM192Cut_layer0)
    (by decide +kernel) vcM192Cut_caps_nonneg vcM192Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM193CutCell) (roots := vcM193CutRoots)
    (caps := vcM193CutCaps) (weightFloor := vcM193CutWeightFloor) (margins := vcM193CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM193Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM193Cut_layer0)
    (by decide +kernel) vcM193Cut_caps_nonneg vcM193Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM194CutCell) (roots := vcM194CutRoots)
    (caps := vcM194CutCaps) (weightFloor := vcM194CutWeightFloor) (margins := vcM194CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM194Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM194Cut_layer0)
    (by decide +kernel) vcM194Cut_caps_nonneg vcM194Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM195CutCell) (roots := vcM195CutRoots)
    (caps := vcM195CutCaps) (weightFloor := vcM195CutWeightFloor) (margins := vcM195CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM195Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM195Cut_layer0)
    (by decide +kernel) vcM195Cut_caps_nonneg vcM195Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM196CutCell) (roots := vcM196CutRoots)
    (caps := vcM196CutCaps) (weightFloor := vcM196CutWeightFloor) (margins := vcM196CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM196Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM196Cut_layer0)
    (by decide +kernel) vcM196Cut_caps_nonneg vcM196Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM197CutCell) (roots := vcM197CutRoots)
    (caps := vcM197CutCaps) (weightFloor := vcM197CutWeightFloor) (margins := vcM197CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM197Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM197Cut_layer0)
    (by decide +kernel) vcM197Cut_caps_nonneg vcM197Cut_margin_le (by decide) (by decide +kernel)]

def vcCutMiddleCertificates192 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcM198CutCell) (roots := vcM198CutRoots)
    (caps := vcM198CutCaps) (weightFloor := vcM198CutWeightFloor) (margins := vcM198CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM198Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM198Cut_layer0)
    (by decide +kernel) vcM198Cut_caps_nonneg vcM198Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM199CutCell) (roots := vcM199CutRoots)
    (caps := vcM199CutCaps) (weightFloor := vcM199CutWeightFloor) (margins := vcM199CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM199Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM199Cut_layer0)
    (by decide +kernel) vcM199Cut_caps_nonneg vcM199Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM200CutCell) (roots := vcM200CutRoots)
    (caps := vcM200CutCaps) (weightFloor := vcM200CutWeightFloor) (margins := vcM200CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM200Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM200Cut_layer0)
    (by decide +kernel) vcM200Cut_caps_nonneg vcM200Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM201CutCell) (roots := vcM201CutRoots)
    (caps := vcM201CutCaps) (weightFloor := vcM201CutWeightFloor) (margins := vcM201CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM201Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM201Cut_layer0)
    (by decide +kernel) vcM201Cut_caps_nonneg vcM201Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM202CutCell) (roots := vcM202CutRoots)
    (caps := vcM202CutCaps) (weightFloor := vcM202CutWeightFloor) (margins := vcM202CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM202Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM202Cut_layer0)
    (by decide +kernel) vcM202Cut_caps_nonneg vcM202Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM203CutCell) (roots := vcM203CutRoots)
    (caps := vcM203CutCaps) (weightFloor := vcM203CutWeightFloor) (margins := vcM203CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM203Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM203Cut_layer0)
    (by decide +kernel) vcM203Cut_caps_nonneg vcM203Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM204CutCell) (roots := vcM204CutRoots)
    (caps := vcM204CutCaps) (weightFloor := vcM204CutWeightFloor) (margins := vcM204CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM204Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM204Cut_layer0)
    (by decide +kernel) vcM204Cut_caps_nonneg vcM204Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM205CutCell) (roots := vcM205CutRoots)
    (caps := vcM205CutCaps) (weightFloor := vcM205CutWeightFloor) (margins := vcM205CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM205Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM205Cut_layer0)
    (by decide +kernel) vcM205Cut_caps_nonneg vcM205Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM206CutCell) (roots := vcM206CutRoots)
    (caps := vcM206CutCaps) (weightFloor := vcM206CutWeightFloor) (margins := vcM206CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM206Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM206Cut_layer0)
    (by decide +kernel) vcM206Cut_caps_nonneg vcM206Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM207CutCell) (roots := vcM207CutRoots)
    (caps := vcM207CutCaps) (weightFloor := vcM207CutWeightFloor) (margins := vcM207CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM207Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM207Cut_layer0)
    (by decide +kernel) vcM207Cut_caps_nonneg vcM207Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM1Child0CutCell) (roots := vcM1Child0CutRoots)
    (caps := vcM1Child0CutCaps) (weightFloor := vcM1Child0CutWeightFloor) (margins := vcM1Child0CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM1Child0Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM1Child0Cut_layer0)
    (by decide +kernel) vcM1Child0Cut_caps_nonneg vcM1Child0Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM1Child1CutCell) (roots := vcM1Child1CutRoots)
    (caps := vcM1Child1CutCaps) (weightFloor := vcM1Child1CutWeightFloor) (margins := vcM1Child1CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM1Child1Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM1Child1Cut_layer0)
    (by decide +kernel) vcM1Child1Cut_caps_nonneg vcM1Child1Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM1Child2CutCell) (roots := vcM1Child2CutRoots)
    (caps := vcM1Child2CutCaps) (weightFloor := vcM1Child2CutWeightFloor) (margins := vcM1Child2CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM1Child2Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM1Child2Cut_layer0)
    (by decide +kernel) vcM1Child2Cut_caps_nonneg vcM1Child2Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM1Child3CutCell) (roots := vcM1Child3CutRoots)
    (caps := vcM1Child3CutCaps) (weightFloor := vcM1Child3CutWeightFloor) (margins := vcM1Child3CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM1Child3Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM1Child3Cut_layer0)
    (by decide +kernel) vcM1Child3Cut_caps_nonneg vcM1Child3Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM1Child4CutCell) (roots := vcM1Child4CutRoots)
    (caps := vcM1Child4CutCaps) (weightFloor := vcM1Child4CutWeightFloor) (margins := vcM1Child4CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM1Child4Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM1Child4Cut_layer0)
    (by decide +kernel) vcM1Child4Cut_caps_nonneg vcM1Child4Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM1Child5CutCell) (roots := vcM1Child5CutRoots)
    (caps := vcM1Child5CutCaps) (weightFloor := vcM1Child5CutWeightFloor) (margins := vcM1Child5CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM1Child5Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM1Child5Cut_layer0)
    (by decide +kernel) vcM1Child5Cut_caps_nonneg vcM1Child5Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM1Child6CutCell) (roots := vcM1Child6CutRoots)
    (caps := vcM1Child6CutCaps) (weightFloor := vcM1Child6CutWeightFloor) (margins := vcM1Child6CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM1Child6Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM1Child6Cut_layer0)
    (by decide +kernel) vcM1Child6Cut_caps_nonneg vcM1Child6Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM1Child7CutCell) (roots := vcM1Child7CutRoots)
    (caps := vcM1Child7CutCaps) (weightFloor := vcM1Child7CutWeightFloor) (margins := vcM1Child7CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM1Child7Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM1Child7Cut_layer0)
    (by decide +kernel) vcM1Child7Cut_caps_nonneg vcM1Child7Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM28Child0CutCell) (roots := vcM28Child0CutRoots)
    (caps := vcM28Child0CutCaps) (weightFloor := vcM28Child0CutWeightFloor) (margins := vcM28Child0CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM28Child0Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM28Child0Cut_layer0)
    (by decide +kernel) vcM28Child0Cut_caps_nonneg vcM28Child0Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM28Child1CutCell) (roots := vcM28Child1CutRoots)
    (caps := vcM28Child1CutCaps) (weightFloor := vcM28Child1CutWeightFloor) (margins := vcM28Child1CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM28Child1Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM28Child1Cut_layer0
      · exact vcM28Child1Cut_layer1)
    (by decide +kernel) vcM28Child1Cut_caps_nonneg vcM28Child1Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM28Child2CutCell) (roots := vcM28Child2CutRoots)
    (caps := vcM28Child2CutCaps) (weightFloor := vcM28Child2CutWeightFloor) (margins := vcM28Child2CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM28Child2Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM28Child2Cut_layer0)
    (by decide +kernel) vcM28Child2Cut_caps_nonneg vcM28Child2Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM28Child3CutCell) (roots := vcM28Child3CutRoots)
    (caps := vcM28Child3CutCaps) (weightFloor := vcM28Child3CutWeightFloor) (margins := vcM28Child3CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM28Child3Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM28Child3Cut_layer0)
    (by decide +kernel) vcM28Child3Cut_caps_nonneg vcM28Child3Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM28Child4CutCell) (roots := vcM28Child4CutRoots)
    (caps := vcM28Child4CutCaps) (weightFloor := vcM28Child4CutWeightFloor) (margins := vcM28Child4CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM28Child4Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM28Child4Cut_layer0)
    (by decide +kernel) vcM28Child4Cut_caps_nonneg vcM28Child4Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM28Child5CutCell) (roots := vcM28Child5CutRoots)
    (caps := vcM28Child5CutCaps) (weightFloor := vcM28Child5CutWeightFloor) (margins := vcM28Child5CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM28Child5Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM28Child5Cut_layer0
      · exact vcM28Child5Cut_layer1)
    (by decide +kernel) vcM28Child5Cut_caps_nonneg vcM28Child5Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM28Child6CutCell) (roots := vcM28Child6CutRoots)
    (caps := vcM28Child6CutCaps) (weightFloor := vcM28Child6CutWeightFloor) (margins := vcM28Child6CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM28Child6Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM28Child6Cut_layer0)
    (by decide +kernel) vcM28Child6Cut_caps_nonneg vcM28Child6Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM28Child7CutCell) (roots := vcM28Child7CutRoots)
    (caps := vcM28Child7CutCaps) (weightFloor := vcM28Child7CutWeightFloor) (margins := vcM28Child7CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM28Child7Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM28Child7Cut_layer0)
    (by decide +kernel) vcM28Child7Cut_caps_nonneg vcM28Child7Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM29Child0CutCell) (roots := vcM29Child0CutRoots)
    (caps := vcM29Child0CutCaps) (weightFloor := vcM29Child0CutWeightFloor) (margins := vcM29Child0CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM29Child0Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM29Child0Cut_layer0
      · exact vcM29Child0Cut_layer1)
    (by decide +kernel) vcM29Child0Cut_caps_nonneg vcM29Child0Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM29Child1CutCell) (roots := vcM29Child1CutRoots)
    (caps := vcM29Child1CutCaps) (weightFloor := vcM29Child1CutWeightFloor) (margins := vcM29Child1CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM29Child1Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM29Child1Cut_layer0
      · exact vcM29Child1Cut_layer1)
    (by decide +kernel) vcM29Child1Cut_caps_nonneg vcM29Child1Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM29Child2CutCell) (roots := vcM29Child2CutRoots)
    (caps := vcM29Child2CutCaps) (weightFloor := vcM29Child2CutWeightFloor) (margins := vcM29Child2CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM29Child2Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM29Child2Cut_layer0)
    (by decide +kernel) vcM29Child2Cut_caps_nonneg vcM29Child2Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM29Child3CutCell) (roots := vcM29Child3CutRoots)
    (caps := vcM29Child3CutCaps) (weightFloor := vcM29Child3CutWeightFloor) (margins := vcM29Child3CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM29Child3Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM29Child3Cut_layer0)
    (by decide +kernel) vcM29Child3Cut_caps_nonneg vcM29Child3Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM29Child4CutCell) (roots := vcM29Child4CutRoots)
    (caps := vcM29Child4CutCaps) (weightFloor := vcM29Child4CutWeightFloor) (margins := vcM29Child4CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM29Child4Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM29Child4Cut_layer0
      · exact vcM29Child4Cut_layer1)
    (by decide +kernel) vcM29Child4Cut_caps_nonneg vcM29Child4Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM29Child5CutCell) (roots := vcM29Child5CutRoots)
    (caps := vcM29Child5CutCaps) (weightFloor := vcM29Child5CutWeightFloor) (margins := vcM29Child5CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM29Child5Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM29Child5Cut_layer0
      · exact vcM29Child5Cut_layer1)
    (by decide +kernel) vcM29Child5Cut_caps_nonneg vcM29Child5Cut_margin_le (by decide) (by decide +kernel)]

def vcCutMiddleCertificates224 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcM29Child6CutCell) (roots := vcM29Child6CutRoots)
    (caps := vcM29Child6CutCaps) (weightFloor := vcM29Child6CutWeightFloor) (margins := vcM29Child6CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM29Child6Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM29Child6Cut_layer0)
    (by decide +kernel) vcM29Child6Cut_caps_nonneg vcM29Child6Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM29Child7CutCell) (roots := vcM29Child7CutRoots)
    (caps := vcM29Child7CutCaps) (weightFloor := vcM29Child7CutWeightFloor) (margins := vcM29Child7CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM29Child7Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM29Child7Cut_layer0)
    (by decide +kernel) vcM29Child7Cut_caps_nonneg vcM29Child7Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM31Child0CutCell) (roots := vcM31Child0CutRoots)
    (caps := vcM31Child0CutCaps) (weightFloor := vcM31Child0CutWeightFloor) (margins := vcM31Child0CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM31Child0Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM31Child0Cut_layer0)
    (by decide +kernel) vcM31Child0Cut_caps_nonneg vcM31Child0Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM31Child1CutCell) (roots := vcM31Child1CutRoots)
    (caps := vcM31Child1CutCaps) (weightFloor := vcM31Child1CutWeightFloor) (margins := vcM31Child1CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM31Child1Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM31Child1Cut_layer0)
    (by decide +kernel) vcM31Child1Cut_caps_nonneg vcM31Child1Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM31Child2CutCell) (roots := vcM31Child2CutRoots)
    (caps := vcM31Child2CutCaps) (weightFloor := vcM31Child2CutWeightFloor) (margins := vcM31Child2CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM31Child2Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM31Child2Cut_layer0)
    (by decide +kernel) vcM31Child2Cut_caps_nonneg vcM31Child2Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM31Child3CutCell) (roots := vcM31Child3CutRoots)
    (caps := vcM31Child3CutCaps) (weightFloor := vcM31Child3CutWeightFloor) (margins := vcM31Child3CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM31Child3Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM31Child3Cut_layer0)
    (by decide +kernel) vcM31Child3Cut_caps_nonneg vcM31Child3Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM31Child4CutCell) (roots := vcM31Child4CutRoots)
    (caps := vcM31Child4CutCaps) (weightFloor := vcM31Child4CutWeightFloor) (margins := vcM31Child4CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM31Child4Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM31Child4Cut_layer0)
    (by decide +kernel) vcM31Child4Cut_caps_nonneg vcM31Child4Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM31Child5CutCell) (roots := vcM31Child5CutRoots)
    (caps := vcM31Child5CutCaps) (weightFloor := vcM31Child5CutWeightFloor) (margins := vcM31Child5CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM31Child5Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM31Child5Cut_layer0)
    (by decide +kernel) vcM31Child5Cut_caps_nonneg vcM31Child5Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM31Child6CutCell) (roots := vcM31Child6CutRoots)
    (caps := vcM31Child6CutCaps) (weightFloor := vcM31Child6CutWeightFloor) (margins := vcM31Child6CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM31Child6Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM31Child6Cut_layer0)
    (by decide +kernel) vcM31Child6Cut_caps_nonneg vcM31Child6Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM31Child7CutCell) (roots := vcM31Child7CutRoots)
    (caps := vcM31Child7CutCaps) (weightFloor := vcM31Child7CutWeightFloor) (margins := vcM31Child7CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM31Child7Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM31Child7Cut_layer0)
    (by decide +kernel) vcM31Child7Cut_caps_nonneg vcM31Child7Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM59Child0CutCell) (roots := vcM59Child0CutRoots)
    (caps := vcM59Child0CutCaps) (weightFloor := vcM59Child0CutWeightFloor) (margins := vcM59Child0CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM59Child0Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM59Child0Cut_layer0
      · exact vcM59Child0Cut_layer1)
    (by decide +kernel) vcM59Child0Cut_caps_nonneg vcM59Child0Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM59Child1CutCell) (roots := vcM59Child1CutRoots)
    (caps := vcM59Child1CutCaps) (weightFloor := vcM59Child1CutWeightFloor) (margins := vcM59Child1CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM59Child1Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM59Child1Cut_layer0
      · exact vcM59Child1Cut_layer1)
    (by decide +kernel) vcM59Child1Cut_caps_nonneg vcM59Child1Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM59Child2CutCell) (roots := vcM59Child2CutRoots)
    (caps := vcM59Child2CutCaps) (weightFloor := vcM59Child2CutWeightFloor) (margins := vcM59Child2CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM59Child2Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM59Child2Cut_layer0)
    (by decide +kernel) vcM59Child2Cut_caps_nonneg vcM59Child2Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM59Child3CutCell) (roots := vcM59Child3CutRoots)
    (caps := vcM59Child3CutCaps) (weightFloor := vcM59Child3CutWeightFloor) (margins := vcM59Child3CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM59Child3Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM59Child3Cut_layer0)
    (by decide +kernel) vcM59Child3Cut_caps_nonneg vcM59Child3Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM59Child4CutCell) (roots := vcM59Child4CutRoots)
    (caps := vcM59Child4CutCaps) (weightFloor := vcM59Child4CutWeightFloor) (margins := vcM59Child4CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM59Child4Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM59Child4Cut_layer0
      · exact vcM59Child4Cut_layer1)
    (by decide +kernel) vcM59Child4Cut_caps_nonneg vcM59Child4Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM59Child5CutCell) (roots := vcM59Child5CutRoots)
    (caps := vcM59Child5CutCaps) (weightFloor := vcM59Child5CutWeightFloor) (margins := vcM59Child5CutMargins)
    (na := 2) (nb := 2) (nη := 1)
    vcM59Child5Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM59Child5Cut_layer0
      · exact vcM59Child5Cut_layer1)
    (by decide +kernel) vcM59Child5Cut_caps_nonneg vcM59Child5Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM59Child6CutCell) (roots := vcM59Child6CutRoots)
    (caps := vcM59Child6CutCaps) (weightFloor := vcM59Child6CutWeightFloor) (margins := vcM59Child6CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM59Child6Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM59Child6Cut_layer0)
    (by decide +kernel) vcM59Child6Cut_caps_nonneg vcM59Child6Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM59Child7CutCell) (roots := vcM59Child7CutRoots)
    (caps := vcM59Child7CutCaps) (weightFloor := vcM59Child7CutWeightFloor) (margins := vcM59Child7CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM59Child7Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM59Child7Cut_layer0)
    (by decide +kernel) vcM59Child7Cut_caps_nonneg vcM59Child7Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM61Child0CutCell) (roots := vcM61Child0CutRoots)
    (caps := vcM61Child0CutCaps) (weightFloor := vcM61Child0CutWeightFloor) (margins := vcM61Child0CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM61Child0Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM61Child0Cut_layer0)
    (by decide +kernel) vcM61Child0Cut_caps_nonneg vcM61Child0Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM61Child1CutCell) (roots := vcM61Child1CutRoots)
    (caps := vcM61Child1CutCaps) (weightFloor := vcM61Child1CutWeightFloor) (margins := vcM61Child1CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM61Child1Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM61Child1Cut_layer0)
    (by decide +kernel) vcM61Child1Cut_caps_nonneg vcM61Child1Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM61Child2CutCell) (roots := vcM61Child2CutRoots)
    (caps := vcM61Child2CutCaps) (weightFloor := vcM61Child2CutWeightFloor) (margins := vcM61Child2CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM61Child2Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM61Child2Cut_layer0)
    (by decide +kernel) vcM61Child2Cut_caps_nonneg vcM61Child2Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM61Child3CutCell) (roots := vcM61Child3CutRoots)
    (caps := vcM61Child3CutCaps) (weightFloor := vcM61Child3CutWeightFloor) (margins := vcM61Child3CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM61Child3Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM61Child3Cut_layer0)
    (by decide +kernel) vcM61Child3Cut_caps_nonneg vcM61Child3Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM61Child4CutCell) (roots := vcM61Child4CutRoots)
    (caps := vcM61Child4CutCaps) (weightFloor := vcM61Child4CutWeightFloor) (margins := vcM61Child4CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM61Child4Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM61Child4Cut_layer0)
    (by decide +kernel) vcM61Child4Cut_caps_nonneg vcM61Child4Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM61Child5CutCell) (roots := vcM61Child5CutRoots)
    (caps := vcM61Child5CutCaps) (weightFloor := vcM61Child5CutWeightFloor) (margins := vcM61Child5CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM61Child5Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM61Child5Cut_layer0)
    (by decide +kernel) vcM61Child5Cut_caps_nonneg vcM61Child5Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM61Child6CutCell) (roots := vcM61Child6CutRoots)
    (caps := vcM61Child6CutCaps) (weightFloor := vcM61Child6CutWeightFloor) (margins := vcM61Child6CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM61Child6Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM61Child6Cut_layer0)
    (by decide +kernel) vcM61Child6Cut_caps_nonneg vcM61Child6Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcM61Child7CutCell) (roots := vcM61Child7CutRoots)
    (caps := vcM61Child7CutCaps) (weightFloor := vcM61Child7CutWeightFloor) (margins := vcM61Child7CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcM61Child7Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcM61Child7Cut_layer0)
    (by decide +kernel) vcM61Child7Cut_caps_nonneg vcM61Child7Cut_margin_le (by decide) (by decide +kernel)]

def vcCutMiddleCertificates : List (CurvatureCellCertificate) :=
  vcCutMiddleCertificates000 ++
  vcCutMiddleCertificates032 ++
  vcCutMiddleCertificates064 ++
  vcCutMiddleCertificates096 ++
  vcCutMiddleCertificates128 ++
  vcCutMiddleCertificates160 ++
  vcCutMiddleCertificates192 ++
  vcCutMiddleCertificates224

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vcCutMiddleCertificates_cells :
    vcCutMiddleCertificates.map CurvatureCellCertificate.cell = vcMiddleRefinedGrid := by
  decide +kernel

end HlawkaSchatten.BelowExponent.Vertex
