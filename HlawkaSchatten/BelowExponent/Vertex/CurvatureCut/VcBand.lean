/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCertificates
public import HlawkaSchatten.BelowExponent.Vertex.VcParameterGrid
meta import Mathlib.Tactic.FinCases
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcBandChecks000
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcBandChecks001
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcBandChecks002
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcBandChecks003
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcBandChecks004
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcBandChecks005
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCut.VcBandChecks006

/-! Checked curvature and weights on the same closed parameter grid. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vcCutBandCertificates000 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcS10CutCell) (roots := vcS10CutRoots)
    (caps := vcS10CutCaps) (weightFloor := vcS10CutWeightFloor) (margins := vcS10CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS10Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS10Cut_layer0)
    (by decide +kernel) vcS10Cut_caps_nonneg vcS10Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS11CutCell) (roots := vcS11CutRoots)
    (caps := vcS11CutCaps) (weightFloor := vcS11CutWeightFloor) (margins := vcS11CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS11Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS11Cut_layer0)
    (by decide +kernel) vcS11Cut_caps_nonneg vcS11Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS12CutCell) (roots := vcS12CutRoots)
    (caps := vcS12CutCaps) (weightFloor := vcS12CutWeightFloor) (margins := vcS12CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS12Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS12Cut_layer0)
    (by decide +kernel) vcS12Cut_caps_nonneg vcS12Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS13CutCell) (roots := vcS13CutRoots)
    (caps := vcS13CutCaps) (weightFloor := vcS13CutWeightFloor) (margins := vcS13CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS13Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS13Cut_layer0)
    (by decide +kernel) vcS13Cut_caps_nonneg vcS13Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS14CutCell) (roots := vcS14CutRoots)
    (caps := vcS14CutCaps) (weightFloor := vcS14CutWeightFloor) (margins := vcS14CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS14Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS14Cut_layer0)
    (by decide +kernel) vcS14Cut_caps_nonneg vcS14Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS15CutCell) (roots := vcS15CutRoots)
    (caps := vcS15CutCaps) (weightFloor := vcS15CutWeightFloor) (margins := vcS15CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS15Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS15Cut_layer0)
    (by decide +kernel) vcS15Cut_caps_nonneg vcS15Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS16CutCell) (roots := vcS16CutRoots)
    (caps := vcS16CutCaps) (weightFloor := vcS16CutWeightFloor) (margins := vcS16CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS16Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS16Cut_layer0)
    (by decide +kernel) vcS16Cut_caps_nonneg vcS16Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS17CutCell) (roots := vcS17CutRoots)
    (caps := vcS17CutCaps) (weightFloor := vcS17CutWeightFloor) (margins := vcS17CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS17Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS17Cut_layer0)
    (by decide +kernel) vcS17Cut_caps_nonneg vcS17Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS18CutCell) (roots := vcS18CutRoots)
    (caps := vcS18CutCaps) (weightFloor := vcS18CutWeightFloor) (margins := vcS18CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS18Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS18Cut_layer0)
    (by decide +kernel) vcS18Cut_caps_nonneg vcS18Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS19CutCell) (roots := vcS19CutRoots)
    (caps := vcS19CutCaps) (weightFloor := vcS19CutWeightFloor) (margins := vcS19CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS19Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS19Cut_layer0)
    (by decide +kernel) vcS19Cut_caps_nonneg vcS19Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS110CutCell) (roots := vcS110CutRoots)
    (caps := vcS110CutCaps) (weightFloor := vcS110CutWeightFloor) (margins := vcS110CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS110Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS110Cut_layer0)
    (by decide +kernel) vcS110Cut_caps_nonneg vcS110Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS111CutCell) (roots := vcS111CutRoots)
    (caps := vcS111CutCaps) (weightFloor := vcS111CutWeightFloor) (margins := vcS111CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS111Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS111Cut_layer0)
    (by decide +kernel) vcS111Cut_caps_nonneg vcS111Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS112CutCell) (roots := vcS112CutRoots)
    (caps := vcS112CutCaps) (weightFloor := vcS112CutWeightFloor) (margins := vcS112CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS112Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS112Cut_layer0)
    (by decide +kernel) vcS112Cut_caps_nonneg vcS112Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS113CutCell) (roots := vcS113CutRoots)
    (caps := vcS113CutCaps) (weightFloor := vcS113CutWeightFloor) (margins := vcS113CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS113Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS113Cut_layer0)
    (by decide +kernel) vcS113Cut_caps_nonneg vcS113Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS114CutCell) (roots := vcS114CutRoots)
    (caps := vcS114CutCaps) (weightFloor := vcS114CutWeightFloor) (margins := vcS114CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS114Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS114Cut_layer0)
    (by decide +kernel) vcS114Cut_caps_nonneg vcS114Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS115CutCell) (roots := vcS115CutRoots)
    (caps := vcS115CutCaps) (weightFloor := vcS115CutWeightFloor) (margins := vcS115CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS115Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS115Cut_layer0)
    (by decide +kernel) vcS115Cut_caps_nonneg vcS115Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS116CutCell) (roots := vcS116CutRoots)
    (caps := vcS116CutCaps) (weightFloor := vcS116CutWeightFloor) (margins := vcS116CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS116Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS116Cut_layer0)
    (by decide +kernel) vcS116Cut_caps_nonneg vcS116Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS117CutCell) (roots := vcS117CutRoots)
    (caps := vcS117CutCaps) (weightFloor := vcS117CutWeightFloor) (margins := vcS117CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS117Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS117Cut_layer0)
    (by decide +kernel) vcS117Cut_caps_nonneg vcS117Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS118CutCell) (roots := vcS118CutRoots)
    (caps := vcS118CutCaps) (weightFloor := vcS118CutWeightFloor) (margins := vcS118CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS118Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS118Cut_layer0)
    (by decide +kernel) vcS118Cut_caps_nonneg vcS118Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS119CutCell) (roots := vcS119CutRoots)
    (caps := vcS119CutCaps) (weightFloor := vcS119CutWeightFloor) (margins := vcS119CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS119Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS119Cut_layer0)
    (by decide +kernel) vcS119Cut_caps_nonneg vcS119Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS120CutCell) (roots := vcS120CutRoots)
    (caps := vcS120CutCaps) (weightFloor := vcS120CutWeightFloor) (margins := vcS120CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS120Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS120Cut_layer0)
    (by decide +kernel) vcS120Cut_caps_nonneg vcS120Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS121CutCell) (roots := vcS121CutRoots)
    (caps := vcS121CutCaps) (weightFloor := vcS121CutWeightFloor) (margins := vcS121CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS121Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS121Cut_layer0)
    (by decide +kernel) vcS121Cut_caps_nonneg vcS121Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS122CutCell) (roots := vcS122CutRoots)
    (caps := vcS122CutCaps) (weightFloor := vcS122CutWeightFloor) (margins := vcS122CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS122Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS122Cut_layer0)
    (by decide +kernel) vcS122Cut_caps_nonneg vcS122Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS123CutCell) (roots := vcS123CutRoots)
    (caps := vcS123CutCaps) (weightFloor := vcS123CutWeightFloor) (margins := vcS123CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS123Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS123Cut_layer0)
    (by decide +kernel) vcS123Cut_caps_nonneg vcS123Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS124CutCell) (roots := vcS124CutRoots)
    (caps := vcS124CutCaps) (weightFloor := vcS124CutWeightFloor) (margins := vcS124CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS124Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS124Cut_layer0)
    (by decide +kernel) vcS124Cut_caps_nonneg vcS124Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS125CutCell) (roots := vcS125CutRoots)
    (caps := vcS125CutCaps) (weightFloor := vcS125CutWeightFloor) (margins := vcS125CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS125Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS125Cut_layer0)
    (by decide +kernel) vcS125Cut_caps_nonneg vcS125Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS126CutCell) (roots := vcS126CutRoots)
    (caps := vcS126CutCaps) (weightFloor := vcS126CutWeightFloor) (margins := vcS126CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS126Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS126Cut_layer0)
    (by decide +kernel) vcS126Cut_caps_nonneg vcS126Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS127CutCell) (roots := vcS127CutRoots)
    (caps := vcS127CutCaps) (weightFloor := vcS127CutWeightFloor) (margins := vcS127CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS127Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS127Cut_layer0)
    (by decide +kernel) vcS127Cut_caps_nonneg vcS127Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS128CutCell) (roots := vcS128CutRoots)
    (caps := vcS128CutCaps) (weightFloor := vcS128CutWeightFloor) (margins := vcS128CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS128Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS128Cut_layer0)
    (by decide +kernel) vcS128Cut_caps_nonneg vcS128Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS129CutCell) (roots := vcS129CutRoots)
    (caps := vcS129CutCaps) (weightFloor := vcS129CutWeightFloor) (margins := vcS129CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS129Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS129Cut_layer0)
    (by decide +kernel) vcS129Cut_caps_nonneg vcS129Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS130CutCell) (roots := vcS130CutRoots)
    (caps := vcS130CutCaps) (weightFloor := vcS130CutWeightFloor) (margins := vcS130CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS130Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS130Cut_layer0)
    (by decide +kernel) vcS130Cut_caps_nonneg vcS130Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS131CutCell) (roots := vcS131CutRoots)
    (caps := vcS131CutCaps) (weightFloor := vcS131CutWeightFloor) (margins := vcS131CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS131Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS131Cut_layer0)
    (by decide +kernel) vcS131Cut_caps_nonneg vcS131Cut_margin_le (by decide) (by decide +kernel)]

def vcCutBandCertificates032 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcS132CutCell) (roots := vcS132CutRoots)
    (caps := vcS132CutCaps) (weightFloor := vcS132CutWeightFloor) (margins := vcS132CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS132Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS132Cut_layer0)
    (by decide +kernel) vcS132Cut_caps_nonneg vcS132Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS133CutCell) (roots := vcS133CutRoots)
    (caps := vcS133CutCaps) (weightFloor := vcS133CutWeightFloor) (margins := vcS133CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS133Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS133Cut_layer0)
    (by decide +kernel) vcS133Cut_caps_nonneg vcS133Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS134CutCell) (roots := vcS134CutRoots)
    (caps := vcS134CutCaps) (weightFloor := vcS134CutWeightFloor) (margins := vcS134CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS134Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS134Cut_layer0)
    (by decide +kernel) vcS134Cut_caps_nonneg vcS134Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS135CutCell) (roots := vcS135CutRoots)
    (caps := vcS135CutCaps) (weightFloor := vcS135CutWeightFloor) (margins := vcS135CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS135Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS135Cut_layer0)
    (by decide +kernel) vcS135Cut_caps_nonneg vcS135Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS136CutCell) (roots := vcS136CutRoots)
    (caps := vcS136CutCaps) (weightFloor := vcS136CutWeightFloor) (margins := vcS136CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS136Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS136Cut_layer0)
    (by decide +kernel) vcS136Cut_caps_nonneg vcS136Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS137CutCell) (roots := vcS137CutRoots)
    (caps := vcS137CutCaps) (weightFloor := vcS137CutWeightFloor) (margins := vcS137CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS137Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS137Cut_layer0)
    (by decide +kernel) vcS137Cut_caps_nonneg vcS137Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS138CutCell) (roots := vcS138CutRoots)
    (caps := vcS138CutCaps) (weightFloor := vcS138CutWeightFloor) (margins := vcS138CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS138Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS138Cut_layer0)
    (by decide +kernel) vcS138Cut_caps_nonneg vcS138Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS139CutCell) (roots := vcS139CutRoots)
    (caps := vcS139CutCaps) (weightFloor := vcS139CutWeightFloor) (margins := vcS139CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS139Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS139Cut_layer0)
    (by decide +kernel) vcS139Cut_caps_nonneg vcS139Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS140CutCell) (roots := vcS140CutRoots)
    (caps := vcS140CutCaps) (weightFloor := vcS140CutWeightFloor) (margins := vcS140CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS140Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS140Cut_layer0)
    (by decide +kernel) vcS140Cut_caps_nonneg vcS140Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS141CutCell) (roots := vcS141CutRoots)
    (caps := vcS141CutCaps) (weightFloor := vcS141CutWeightFloor) (margins := vcS141CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS141Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS141Cut_layer0)
    (by decide +kernel) vcS141Cut_caps_nonneg vcS141Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS142CutCell) (roots := vcS142CutRoots)
    (caps := vcS142CutCaps) (weightFloor := vcS142CutWeightFloor) (margins := vcS142CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS142Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS142Cut_layer0)
    (by decide +kernel) vcS142Cut_caps_nonneg vcS142Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS143CutCell) (roots := vcS143CutRoots)
    (caps := vcS143CutCaps) (weightFloor := vcS143CutWeightFloor) (margins := vcS143CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS143Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS143Cut_layer0)
    (by decide +kernel) vcS143Cut_caps_nonneg vcS143Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS144CutCell) (roots := vcS144CutRoots)
    (caps := vcS144CutCaps) (weightFloor := vcS144CutWeightFloor) (margins := vcS144CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS144Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS144Cut_layer0)
    (by decide +kernel) vcS144Cut_caps_nonneg vcS144Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS145CutCell) (roots := vcS145CutRoots)
    (caps := vcS145CutCaps) (weightFloor := vcS145CutWeightFloor) (margins := vcS145CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS145Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS145Cut_layer0)
    (by decide +kernel) vcS145Cut_caps_nonneg vcS145Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS146CutCell) (roots := vcS146CutRoots)
    (caps := vcS146CutCaps) (weightFloor := vcS146CutWeightFloor) (margins := vcS146CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS146Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS146Cut_layer0)
    (by decide +kernel) vcS146Cut_caps_nonneg vcS146Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS147CutCell) (roots := vcS147CutRoots)
    (caps := vcS147CutCaps) (weightFloor := vcS147CutWeightFloor) (margins := vcS147CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS147Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS147Cut_layer0)
    (by decide +kernel) vcS147Cut_caps_nonneg vcS147Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS148CutCell) (roots := vcS148CutRoots)
    (caps := vcS148CutCaps) (weightFloor := vcS148CutWeightFloor) (margins := vcS148CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS148Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS148Cut_layer0)
    (by decide +kernel) vcS148Cut_caps_nonneg vcS148Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS149CutCell) (roots := vcS149CutRoots)
    (caps := vcS149CutCaps) (weightFloor := vcS149CutWeightFloor) (margins := vcS149CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS149Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS149Cut_layer0)
    (by decide +kernel) vcS149Cut_caps_nonneg vcS149Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS150CutCell) (roots := vcS150CutRoots)
    (caps := vcS150CutCaps) (weightFloor := vcS150CutWeightFloor) (margins := vcS150CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS150Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS150Cut_layer0)
    (by decide +kernel) vcS150Cut_caps_nonneg vcS150Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS151CutCell) (roots := vcS151CutRoots)
    (caps := vcS151CutCaps) (weightFloor := vcS151CutWeightFloor) (margins := vcS151CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS151Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS151Cut_layer0)
    (by decide +kernel) vcS151Cut_caps_nonneg vcS151Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS152CutCell) (roots := vcS152CutRoots)
    (caps := vcS152CutCaps) (weightFloor := vcS152CutWeightFloor) (margins := vcS152CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS152Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS152Cut_layer0)
    (by decide +kernel) vcS152Cut_caps_nonneg vcS152Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS153CutCell) (roots := vcS153CutRoots)
    (caps := vcS153CutCaps) (weightFloor := vcS153CutWeightFloor) (margins := vcS153CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS153Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS153Cut_layer0)
    (by decide +kernel) vcS153Cut_caps_nonneg vcS153Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS154CutCell) (roots := vcS154CutRoots)
    (caps := vcS154CutCaps) (weightFloor := vcS154CutWeightFloor) (margins := vcS154CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS154Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS154Cut_layer0)
    (by decide +kernel) vcS154Cut_caps_nonneg vcS154Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS155CutCell) (roots := vcS155CutRoots)
    (caps := vcS155CutCaps) (weightFloor := vcS155CutWeightFloor) (margins := vcS155CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS155Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS155Cut_layer0)
    (by decide +kernel) vcS155Cut_caps_nonneg vcS155Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS156CutCell) (roots := vcS156CutRoots)
    (caps := vcS156CutCaps) (weightFloor := vcS156CutWeightFloor) (margins := vcS156CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS156Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS156Cut_layer0)
    (by decide +kernel) vcS156Cut_caps_nonneg vcS156Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS157CutCell) (roots := vcS157CutRoots)
    (caps := vcS157CutCaps) (weightFloor := vcS157CutWeightFloor) (margins := vcS157CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS157Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS157Cut_layer0)
    (by decide +kernel) vcS157Cut_caps_nonneg vcS157Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS158CutCell) (roots := vcS158CutRoots)
    (caps := vcS158CutCaps) (weightFloor := vcS158CutWeightFloor) (margins := vcS158CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS158Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS158Cut_layer0)
    (by decide +kernel) vcS158Cut_caps_nonneg vcS158Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS159CutCell) (roots := vcS159CutRoots)
    (caps := vcS159CutCaps) (weightFloor := vcS159CutWeightFloor) (margins := vcS159CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS159Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS159Cut_layer0)
    (by decide +kernel) vcS159Cut_caps_nonneg vcS159Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS160CutCell) (roots := vcS160CutRoots)
    (caps := vcS160CutCaps) (weightFloor := vcS160CutWeightFloor) (margins := vcS160CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS160Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS160Cut_layer0)
    (by decide +kernel) vcS160Cut_caps_nonneg vcS160Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS161CutCell) (roots := vcS161CutRoots)
    (caps := vcS161CutCaps) (weightFloor := vcS161CutWeightFloor) (margins := vcS161CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS161Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS161Cut_layer0)
    (by decide +kernel) vcS161Cut_caps_nonneg vcS161Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS162CutCell) (roots := vcS162CutRoots)
    (caps := vcS162CutCaps) (weightFloor := vcS162CutWeightFloor) (margins := vcS162CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS162Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS162Cut_layer0)
    (by decide +kernel) vcS162Cut_caps_nonneg vcS162Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS163CutCell) (roots := vcS163CutRoots)
    (caps := vcS163CutCaps) (weightFloor := vcS163CutWeightFloor) (margins := vcS163CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS163Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS163Cut_layer0)
    (by decide +kernel) vcS163Cut_caps_nonneg vcS163Cut_margin_le (by decide) (by decide +kernel)]

def vcCutBandCertificates064 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcS164CutCell) (roots := vcS164CutRoots)
    (caps := vcS164CutCaps) (weightFloor := vcS164CutWeightFloor) (margins := vcS164CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS164Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS164Cut_layer0)
    (by decide +kernel) vcS164Cut_caps_nonneg vcS164Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS165CutCell) (roots := vcS165CutRoots)
    (caps := vcS165CutCaps) (weightFloor := vcS165CutWeightFloor) (margins := vcS165CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS165Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS165Cut_layer0)
    (by decide +kernel) vcS165Cut_caps_nonneg vcS165Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS166CutCell) (roots := vcS166CutRoots)
    (caps := vcS166CutCaps) (weightFloor := vcS166CutWeightFloor) (margins := vcS166CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS166Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS166Cut_layer0)
    (by decide +kernel) vcS166Cut_caps_nonneg vcS166Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS167CutCell) (roots := vcS167CutRoots)
    (caps := vcS167CutCaps) (weightFloor := vcS167CutWeightFloor) (margins := vcS167CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS167Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS167Cut_layer0)
    (by decide +kernel) vcS167Cut_caps_nonneg vcS167Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS168CutCell) (roots := vcS168CutRoots)
    (caps := vcS168CutCaps) (weightFloor := vcS168CutWeightFloor) (margins := vcS168CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS168Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS168Cut_layer0)
    (by decide +kernel) vcS168Cut_caps_nonneg vcS168Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS169CutCell) (roots := vcS169CutRoots)
    (caps := vcS169CutCaps) (weightFloor := vcS169CutWeightFloor) (margins := vcS169CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS169Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS169Cut_layer0)
    (by decide +kernel) vcS169Cut_caps_nonneg vcS169Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS170CutCell) (roots := vcS170CutRoots)
    (caps := vcS170CutCaps) (weightFloor := vcS170CutWeightFloor) (margins := vcS170CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS170Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS170Cut_layer0)
    (by decide +kernel) vcS170Cut_caps_nonneg vcS170Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS171CutCell) (roots := vcS171CutRoots)
    (caps := vcS171CutCaps) (weightFloor := vcS171CutWeightFloor) (margins := vcS171CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS171Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS171Cut_layer0)
    (by decide +kernel) vcS171Cut_caps_nonneg vcS171Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS172CutCell) (roots := vcS172CutRoots)
    (caps := vcS172CutCaps) (weightFloor := vcS172CutWeightFloor) (margins := vcS172CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS172Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS172Cut_layer0)
    (by decide +kernel) vcS172Cut_caps_nonneg vcS172Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS173CutCell) (roots := vcS173CutRoots)
    (caps := vcS173CutCaps) (weightFloor := vcS173CutWeightFloor) (margins := vcS173CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS173Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS173Cut_layer0)
    (by decide +kernel) vcS173Cut_caps_nonneg vcS173Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS174CutCell) (roots := vcS174CutRoots)
    (caps := vcS174CutCaps) (weightFloor := vcS174CutWeightFloor) (margins := vcS174CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS174Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS174Cut_layer0)
    (by decide +kernel) vcS174Cut_caps_nonneg vcS174Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS175CutCell) (roots := vcS175CutRoots)
    (caps := vcS175CutCaps) (weightFloor := vcS175CutWeightFloor) (margins := vcS175CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS175Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS175Cut_layer0)
    (by decide +kernel) vcS175Cut_caps_nonneg vcS175Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS176CutCell) (roots := vcS176CutRoots)
    (caps := vcS176CutCaps) (weightFloor := vcS176CutWeightFloor) (margins := vcS176CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS176Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS176Cut_layer0)
    (by decide +kernel) vcS176Cut_caps_nonneg vcS176Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS177CutCell) (roots := vcS177CutRoots)
    (caps := vcS177CutCaps) (weightFloor := vcS177CutWeightFloor) (margins := vcS177CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS177Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS177Cut_layer0)
    (by decide +kernel) vcS177Cut_caps_nonneg vcS177Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS178CutCell) (roots := vcS178CutRoots)
    (caps := vcS178CutCaps) (weightFloor := vcS178CutWeightFloor) (margins := vcS178CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS178Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS178Cut_layer0)
    (by decide +kernel) vcS178Cut_caps_nonneg vcS178Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS179CutCell) (roots := vcS179CutRoots)
    (caps := vcS179CutCaps) (weightFloor := vcS179CutWeightFloor) (margins := vcS179CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS179Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS179Cut_layer0)
    (by decide +kernel) vcS179Cut_caps_nonneg vcS179Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS180CutCell) (roots := vcS180CutRoots)
    (caps := vcS180CutCaps) (weightFloor := vcS180CutWeightFloor) (margins := vcS180CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS180Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS180Cut_layer0)
    (by decide +kernel) vcS180Cut_caps_nonneg vcS180Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS181CutCell) (roots := vcS181CutRoots)
    (caps := vcS181CutCaps) (weightFloor := vcS181CutWeightFloor) (margins := vcS181CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS181Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS181Cut_layer0)
    (by decide +kernel) vcS181Cut_caps_nonneg vcS181Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS182CutCell) (roots := vcS182CutRoots)
    (caps := vcS182CutCaps) (weightFloor := vcS182CutWeightFloor) (margins := vcS182CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS182Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS182Cut_layer0)
    (by decide +kernel) vcS182Cut_caps_nonneg vcS182Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS183CutCell) (roots := vcS183CutRoots)
    (caps := vcS183CutCaps) (weightFloor := vcS183CutWeightFloor) (margins := vcS183CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS183Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS183Cut_layer0)
    (by decide +kernel) vcS183Cut_caps_nonneg vcS183Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS184CutCell) (roots := vcS184CutRoots)
    (caps := vcS184CutCaps) (weightFloor := vcS184CutWeightFloor) (margins := vcS184CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS184Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS184Cut_layer0)
    (by decide +kernel) vcS184Cut_caps_nonneg vcS184Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS185CutCell) (roots := vcS185CutRoots)
    (caps := vcS185CutCaps) (weightFloor := vcS185CutWeightFloor) (margins := vcS185CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS185Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS185Cut_layer0)
    (by decide +kernel) vcS185Cut_caps_nonneg vcS185Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS186CutCell) (roots := vcS186CutRoots)
    (caps := vcS186CutCaps) (weightFloor := vcS186CutWeightFloor) (margins := vcS186CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS186Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS186Cut_layer0)
    (by decide +kernel) vcS186Cut_caps_nonneg vcS186Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS187CutCell) (roots := vcS187CutRoots)
    (caps := vcS187CutCaps) (weightFloor := vcS187CutWeightFloor) (margins := vcS187CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS187Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS187Cut_layer0)
    (by decide +kernel) vcS187Cut_caps_nonneg vcS187Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS188CutCell) (roots := vcS188CutRoots)
    (caps := vcS188CutCaps) (weightFloor := vcS188CutWeightFloor) (margins := vcS188CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS188Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS188Cut_layer0)
    (by decide +kernel) vcS188Cut_caps_nonneg vcS188Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS189CutCell) (roots := vcS189CutRoots)
    (caps := vcS189CutCaps) (weightFloor := vcS189CutWeightFloor) (margins := vcS189CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS189Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS189Cut_layer0)
    (by decide +kernel) vcS189Cut_caps_nonneg vcS189Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS190CutCell) (roots := vcS190CutRoots)
    (caps := vcS190CutCaps) (weightFloor := vcS190CutWeightFloor) (margins := vcS190CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS190Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS190Cut_layer0)
    (by decide +kernel) vcS190Cut_caps_nonneg vcS190Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS191CutCell) (roots := vcS191CutRoots)
    (caps := vcS191CutCaps) (weightFloor := vcS191CutWeightFloor) (margins := vcS191CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS191Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS191Cut_layer0)
    (by decide +kernel) vcS191Cut_caps_nonneg vcS191Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS192CutCell) (roots := vcS192CutRoots)
    (caps := vcS192CutCaps) (weightFloor := vcS192CutWeightFloor) (margins := vcS192CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS192Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS192Cut_layer0)
    (by decide +kernel) vcS192Cut_caps_nonneg vcS192Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS193CutCell) (roots := vcS193CutRoots)
    (caps := vcS193CutCaps) (weightFloor := vcS193CutWeightFloor) (margins := vcS193CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS193Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS193Cut_layer0)
    (by decide +kernel) vcS193Cut_caps_nonneg vcS193Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS194CutCell) (roots := vcS194CutRoots)
    (caps := vcS194CutCaps) (weightFloor := vcS194CutWeightFloor) (margins := vcS194CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS194Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS194Cut_layer0)
    (by decide +kernel) vcS194Cut_caps_nonneg vcS194Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS195CutCell) (roots := vcS195CutRoots)
    (caps := vcS195CutCaps) (weightFloor := vcS195CutWeightFloor) (margins := vcS195CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS195Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS195Cut_layer0)
    (by decide +kernel) vcS195Cut_caps_nonneg vcS195Cut_margin_le (by decide) (by decide +kernel)]

def vcCutBandCertificates096 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcS196CutCell) (roots := vcS196CutRoots)
    (caps := vcS196CutCaps) (weightFloor := vcS196CutWeightFloor) (margins := vcS196CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS196Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS196Cut_layer0)
    (by decide +kernel) vcS196Cut_caps_nonneg vcS196Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS197CutCell) (roots := vcS197CutRoots)
    (caps := vcS197CutCaps) (weightFloor := vcS197CutWeightFloor) (margins := vcS197CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS197Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS197Cut_layer0)
    (by decide +kernel) vcS197Cut_caps_nonneg vcS197Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS198CutCell) (roots := vcS198CutRoots)
    (caps := vcS198CutCaps) (weightFloor := vcS198CutWeightFloor) (margins := vcS198CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS198Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS198Cut_layer0)
    (by decide +kernel) vcS198Cut_caps_nonneg vcS198Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS199CutCell) (roots := vcS199CutRoots)
    (caps := vcS199CutCaps) (weightFloor := vcS199CutWeightFloor) (margins := vcS199CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS199Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS199Cut_layer0)
    (by decide +kernel) vcS199Cut_caps_nonneg vcS199Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1100CutCell) (roots := vcS1100CutRoots)
    (caps := vcS1100CutCaps) (weightFloor := vcS1100CutWeightFloor) (margins := vcS1100CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1100Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1100Cut_layer0)
    (by decide +kernel) vcS1100Cut_caps_nonneg vcS1100Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1101CutCell) (roots := vcS1101CutRoots)
    (caps := vcS1101CutCaps) (weightFloor := vcS1101CutWeightFloor) (margins := vcS1101CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1101Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1101Cut_layer0)
    (by decide +kernel) vcS1101Cut_caps_nonneg vcS1101Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1102CutCell) (roots := vcS1102CutRoots)
    (caps := vcS1102CutCaps) (weightFloor := vcS1102CutWeightFloor) (margins := vcS1102CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1102Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1102Cut_layer0)
    (by decide +kernel) vcS1102Cut_caps_nonneg vcS1102Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1103CutCell) (roots := vcS1103CutRoots)
    (caps := vcS1103CutCaps) (weightFloor := vcS1103CutWeightFloor) (margins := vcS1103CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1103Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1103Cut_layer0)
    (by decide +kernel) vcS1103Cut_caps_nonneg vcS1103Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1104CutCell) (roots := vcS1104CutRoots)
    (caps := vcS1104CutCaps) (weightFloor := vcS1104CutWeightFloor) (margins := vcS1104CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1104Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1104Cut_layer0)
    (by decide +kernel) vcS1104Cut_caps_nonneg vcS1104Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1105CutCell) (roots := vcS1105CutRoots)
    (caps := vcS1105CutCaps) (weightFloor := vcS1105CutWeightFloor) (margins := vcS1105CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1105Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1105Cut_layer0)
    (by decide +kernel) vcS1105Cut_caps_nonneg vcS1105Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1106CutCell) (roots := vcS1106CutRoots)
    (caps := vcS1106CutCaps) (weightFloor := vcS1106CutWeightFloor) (margins := vcS1106CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1106Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1106Cut_layer0)
    (by decide +kernel) vcS1106Cut_caps_nonneg vcS1106Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1107CutCell) (roots := vcS1107CutRoots)
    (caps := vcS1107CutCaps) (weightFloor := vcS1107CutWeightFloor) (margins := vcS1107CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1107Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1107Cut_layer0)
    (by decide +kernel) vcS1107Cut_caps_nonneg vcS1107Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1108CutCell) (roots := vcS1108CutRoots)
    (caps := vcS1108CutCaps) (weightFloor := vcS1108CutWeightFloor) (margins := vcS1108CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1108Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1108Cut_layer0)
    (by decide +kernel) vcS1108Cut_caps_nonneg vcS1108Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1109CutCell) (roots := vcS1109CutRoots)
    (caps := vcS1109CutCaps) (weightFloor := vcS1109CutWeightFloor) (margins := vcS1109CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1109Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1109Cut_layer0)
    (by decide +kernel) vcS1109Cut_caps_nonneg vcS1109Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1110CutCell) (roots := vcS1110CutRoots)
    (caps := vcS1110CutCaps) (weightFloor := vcS1110CutWeightFloor) (margins := vcS1110CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1110Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1110Cut_layer0)
    (by decide +kernel) vcS1110Cut_caps_nonneg vcS1110Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1111CutCell) (roots := vcS1111CutRoots)
    (caps := vcS1111CutCaps) (weightFloor := vcS1111CutWeightFloor) (margins := vcS1111CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1111Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1111Cut_layer0)
    (by decide +kernel) vcS1111Cut_caps_nonneg vcS1111Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1112CutCell) (roots := vcS1112CutRoots)
    (caps := vcS1112CutCaps) (weightFloor := vcS1112CutWeightFloor) (margins := vcS1112CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1112Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1112Cut_layer0)
    (by decide +kernel) vcS1112Cut_caps_nonneg vcS1112Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1113CutCell) (roots := vcS1113CutRoots)
    (caps := vcS1113CutCaps) (weightFloor := vcS1113CutWeightFloor) (margins := vcS1113CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1113Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1113Cut_layer0)
    (by decide +kernel) vcS1113Cut_caps_nonneg vcS1113Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1114CutCell) (roots := vcS1114CutRoots)
    (caps := vcS1114CutCaps) (weightFloor := vcS1114CutWeightFloor) (margins := vcS1114CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1114Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1114Cut_layer0)
    (by decide +kernel) vcS1114Cut_caps_nonneg vcS1114Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1115CutCell) (roots := vcS1115CutRoots)
    (caps := vcS1115CutCaps) (weightFloor := vcS1115CutWeightFloor) (margins := vcS1115CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1115Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1115Cut_layer0)
    (by decide +kernel) vcS1115Cut_caps_nonneg vcS1115Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1116CutCell) (roots := vcS1116CutRoots)
    (caps := vcS1116CutCaps) (weightFloor := vcS1116CutWeightFloor) (margins := vcS1116CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1116Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1116Cut_layer0)
    (by decide +kernel) vcS1116Cut_caps_nonneg vcS1116Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1117CutCell) (roots := vcS1117CutRoots)
    (caps := vcS1117CutCaps) (weightFloor := vcS1117CutWeightFloor) (margins := vcS1117CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1117Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1117Cut_layer0)
    (by decide +kernel) vcS1117Cut_caps_nonneg vcS1117Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1118CutCell) (roots := vcS1118CutRoots)
    (caps := vcS1118CutCaps) (weightFloor := vcS1118CutWeightFloor) (margins := vcS1118CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1118Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1118Cut_layer0)
    (by decide +kernel) vcS1118Cut_caps_nonneg vcS1118Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1119CutCell) (roots := vcS1119CutRoots)
    (caps := vcS1119CutCaps) (weightFloor := vcS1119CutWeightFloor) (margins := vcS1119CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1119Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1119Cut_layer0)
    (by decide +kernel) vcS1119Cut_caps_nonneg vcS1119Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1120CutCell) (roots := vcS1120CutRoots)
    (caps := vcS1120CutCaps) (weightFloor := vcS1120CutWeightFloor) (margins := vcS1120CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1120Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1120Cut_layer0)
    (by decide +kernel) vcS1120Cut_caps_nonneg vcS1120Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1121CutCell) (roots := vcS1121CutRoots)
    (caps := vcS1121CutCaps) (weightFloor := vcS1121CutWeightFloor) (margins := vcS1121CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1121Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1121Cut_layer0)
    (by decide +kernel) vcS1121Cut_caps_nonneg vcS1121Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1122CutCell) (roots := vcS1122CutRoots)
    (caps := vcS1122CutCaps) (weightFloor := vcS1122CutWeightFloor) (margins := vcS1122CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1122Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1122Cut_layer0)
    (by decide +kernel) vcS1122Cut_caps_nonneg vcS1122Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1123CutCell) (roots := vcS1123CutRoots)
    (caps := vcS1123CutCaps) (weightFloor := vcS1123CutWeightFloor) (margins := vcS1123CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1123Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1123Cut_layer0)
    (by decide +kernel) vcS1123Cut_caps_nonneg vcS1123Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1124CutCell) (roots := vcS1124CutRoots)
    (caps := vcS1124CutCaps) (weightFloor := vcS1124CutWeightFloor) (margins := vcS1124CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1124Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1124Cut_layer0)
    (by decide +kernel) vcS1124Cut_caps_nonneg vcS1124Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1125CutCell) (roots := vcS1125CutRoots)
    (caps := vcS1125CutCaps) (weightFloor := vcS1125CutWeightFloor) (margins := vcS1125CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1125Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1125Cut_layer0)
    (by decide +kernel) vcS1125Cut_caps_nonneg vcS1125Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1126CutCell) (roots := vcS1126CutRoots)
    (caps := vcS1126CutCaps) (weightFloor := vcS1126CutWeightFloor) (margins := vcS1126CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1126Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1126Cut_layer0)
    (by decide +kernel) vcS1126Cut_caps_nonneg vcS1126Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1127CutCell) (roots := vcS1127CutRoots)
    (caps := vcS1127CutCaps) (weightFloor := vcS1127CutWeightFloor) (margins := vcS1127CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1127Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1127Cut_layer0)
    (by decide +kernel) vcS1127Cut_caps_nonneg vcS1127Cut_margin_le (by decide) (by decide +kernel)]

def vcCutBandCertificates128 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcS1128CutCell) (roots := vcS1128CutRoots)
    (caps := vcS1128CutCaps) (weightFloor := vcS1128CutWeightFloor) (margins := vcS1128CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1128Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1128Cut_layer0)
    (by decide +kernel) vcS1128Cut_caps_nonneg vcS1128Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1129CutCell) (roots := vcS1129CutRoots)
    (caps := vcS1129CutCaps) (weightFloor := vcS1129CutWeightFloor) (margins := vcS1129CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1129Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1129Cut_layer0)
    (by decide +kernel) vcS1129Cut_caps_nonneg vcS1129Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1130CutCell) (roots := vcS1130CutRoots)
    (caps := vcS1130CutCaps) (weightFloor := vcS1130CutWeightFloor) (margins := vcS1130CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1130Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1130Cut_layer0)
    (by decide +kernel) vcS1130Cut_caps_nonneg vcS1130Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1131CutCell) (roots := vcS1131CutRoots)
    (caps := vcS1131CutCaps) (weightFloor := vcS1131CutWeightFloor) (margins := vcS1131CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1131Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1131Cut_layer0)
    (by decide +kernel) vcS1131Cut_caps_nonneg vcS1131Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1132CutCell) (roots := vcS1132CutRoots)
    (caps := vcS1132CutCaps) (weightFloor := vcS1132CutWeightFloor) (margins := vcS1132CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1132Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1132Cut_layer0)
    (by decide +kernel) vcS1132Cut_caps_nonneg vcS1132Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1133CutCell) (roots := vcS1133CutRoots)
    (caps := vcS1133CutCaps) (weightFloor := vcS1133CutWeightFloor) (margins := vcS1133CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1133Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1133Cut_layer0)
    (by decide +kernel) vcS1133Cut_caps_nonneg vcS1133Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1134CutCell) (roots := vcS1134CutRoots)
    (caps := vcS1134CutCaps) (weightFloor := vcS1134CutWeightFloor) (margins := vcS1134CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1134Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1134Cut_layer0)
    (by decide +kernel) vcS1134Cut_caps_nonneg vcS1134Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1135CutCell) (roots := vcS1135CutRoots)
    (caps := vcS1135CutCaps) (weightFloor := vcS1135CutWeightFloor) (margins := vcS1135CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1135Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1135Cut_layer0)
    (by decide +kernel) vcS1135Cut_caps_nonneg vcS1135Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1136CutCell) (roots := vcS1136CutRoots)
    (caps := vcS1136CutCaps) (weightFloor := vcS1136CutWeightFloor) (margins := vcS1136CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1136Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1136Cut_layer0)
    (by decide +kernel) vcS1136Cut_caps_nonneg vcS1136Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1137CutCell) (roots := vcS1137CutRoots)
    (caps := vcS1137CutCaps) (weightFloor := vcS1137CutWeightFloor) (margins := vcS1137CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1137Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1137Cut_layer0)
    (by decide +kernel) vcS1137Cut_caps_nonneg vcS1137Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1138CutCell) (roots := vcS1138CutRoots)
    (caps := vcS1138CutCaps) (weightFloor := vcS1138CutWeightFloor) (margins := vcS1138CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1138Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1138Cut_layer0)
    (by decide +kernel) vcS1138Cut_caps_nonneg vcS1138Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1139CutCell) (roots := vcS1139CutRoots)
    (caps := vcS1139CutCaps) (weightFloor := vcS1139CutWeightFloor) (margins := vcS1139CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1139Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1139Cut_layer0)
    (by decide +kernel) vcS1139Cut_caps_nonneg vcS1139Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1140CutCell) (roots := vcS1140CutRoots)
    (caps := vcS1140CutCaps) (weightFloor := vcS1140CutWeightFloor) (margins := vcS1140CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1140Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1140Cut_layer0)
    (by decide +kernel) vcS1140Cut_caps_nonneg vcS1140Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1141CutCell) (roots := vcS1141CutRoots)
    (caps := vcS1141CutCaps) (weightFloor := vcS1141CutWeightFloor) (margins := vcS1141CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1141Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1141Cut_layer0)
    (by decide +kernel) vcS1141Cut_caps_nonneg vcS1141Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1142CutCell) (roots := vcS1142CutRoots)
    (caps := vcS1142CutCaps) (weightFloor := vcS1142CutWeightFloor) (margins := vcS1142CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1142Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1142Cut_layer0)
    (by decide +kernel) vcS1142Cut_caps_nonneg vcS1142Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1143CutCell) (roots := vcS1143CutRoots)
    (caps := vcS1143CutCaps) (weightFloor := vcS1143CutWeightFloor) (margins := vcS1143CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1143Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1143Cut_layer0)
    (by decide +kernel) vcS1143Cut_caps_nonneg vcS1143Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1144CutCell) (roots := vcS1144CutRoots)
    (caps := vcS1144CutCaps) (weightFloor := vcS1144CutWeightFloor) (margins := vcS1144CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1144Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1144Cut_layer0)
    (by decide +kernel) vcS1144Cut_caps_nonneg vcS1144Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1145CutCell) (roots := vcS1145CutRoots)
    (caps := vcS1145CutCaps) (weightFloor := vcS1145CutWeightFloor) (margins := vcS1145CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1145Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1145Cut_layer0)
    (by decide +kernel) vcS1145Cut_caps_nonneg vcS1145Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1146CutCell) (roots := vcS1146CutRoots)
    (caps := vcS1146CutCaps) (weightFloor := vcS1146CutWeightFloor) (margins := vcS1146CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1146Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1146Cut_layer0)
    (by decide +kernel) vcS1146Cut_caps_nonneg vcS1146Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1147CutCell) (roots := vcS1147CutRoots)
    (caps := vcS1147CutCaps) (weightFloor := vcS1147CutWeightFloor) (margins := vcS1147CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1147Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1147Cut_layer0)
    (by decide +kernel) vcS1147Cut_caps_nonneg vcS1147Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1148CutCell) (roots := vcS1148CutRoots)
    (caps := vcS1148CutCaps) (weightFloor := vcS1148CutWeightFloor) (margins := vcS1148CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1148Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1148Cut_layer0)
    (by decide +kernel) vcS1148Cut_caps_nonneg vcS1148Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1149CutCell) (roots := vcS1149CutRoots)
    (caps := vcS1149CutCaps) (weightFloor := vcS1149CutWeightFloor) (margins := vcS1149CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1149Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1149Cut_layer0)
    (by decide +kernel) vcS1149Cut_caps_nonneg vcS1149Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1150CutCell) (roots := vcS1150CutRoots)
    (caps := vcS1150CutCaps) (weightFloor := vcS1150CutWeightFloor) (margins := vcS1150CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1150Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1150Cut_layer0)
    (by decide +kernel) vcS1150Cut_caps_nonneg vcS1150Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1151CutCell) (roots := vcS1151CutRoots)
    (caps := vcS1151CutCaps) (weightFloor := vcS1151CutWeightFloor) (margins := vcS1151CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1151Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1151Cut_layer0)
    (by decide +kernel) vcS1151Cut_caps_nonneg vcS1151Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1152CutCell) (roots := vcS1152CutRoots)
    (caps := vcS1152CutCaps) (weightFloor := vcS1152CutWeightFloor) (margins := vcS1152CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1152Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1152Cut_layer0)
    (by decide +kernel) vcS1152Cut_caps_nonneg vcS1152Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1153CutCell) (roots := vcS1153CutRoots)
    (caps := vcS1153CutCaps) (weightFloor := vcS1153CutWeightFloor) (margins := vcS1153CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1153Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1153Cut_layer0)
    (by decide +kernel) vcS1153Cut_caps_nonneg vcS1153Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1154CutCell) (roots := vcS1154CutRoots)
    (caps := vcS1154CutCaps) (weightFloor := vcS1154CutWeightFloor) (margins := vcS1154CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1154Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1154Cut_layer0)
    (by decide +kernel) vcS1154Cut_caps_nonneg vcS1154Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1155CutCell) (roots := vcS1155CutRoots)
    (caps := vcS1155CutCaps) (weightFloor := vcS1155CutWeightFloor) (margins := vcS1155CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1155Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1155Cut_layer0)
    (by decide +kernel) vcS1155Cut_caps_nonneg vcS1155Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1156CutCell) (roots := vcS1156CutRoots)
    (caps := vcS1156CutCaps) (weightFloor := vcS1156CutWeightFloor) (margins := vcS1156CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1156Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1156Cut_layer0)
    (by decide +kernel) vcS1156Cut_caps_nonneg vcS1156Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1157CutCell) (roots := vcS1157CutRoots)
    (caps := vcS1157CutCaps) (weightFloor := vcS1157CutWeightFloor) (margins := vcS1157CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1157Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1157Cut_layer0)
    (by decide +kernel) vcS1157Cut_caps_nonneg vcS1157Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1158CutCell) (roots := vcS1158CutRoots)
    (caps := vcS1158CutCaps) (weightFloor := vcS1158CutWeightFloor) (margins := vcS1158CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1158Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1158Cut_layer0)
    (by decide +kernel) vcS1158Cut_caps_nonneg vcS1158Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1159CutCell) (roots := vcS1159CutRoots)
    (caps := vcS1159CutCaps) (weightFloor := vcS1159CutWeightFloor) (margins := vcS1159CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1159Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1159Cut_layer0)
    (by decide +kernel) vcS1159Cut_caps_nonneg vcS1159Cut_margin_le (by decide) (by decide +kernel)]

def vcCutBandCertificates160 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcS1160CutCell) (roots := vcS1160CutRoots)
    (caps := vcS1160CutCaps) (weightFloor := vcS1160CutWeightFloor) (margins := vcS1160CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1160Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1160Cut_layer0)
    (by decide +kernel) vcS1160Cut_caps_nonneg vcS1160Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1161CutCell) (roots := vcS1161CutRoots)
    (caps := vcS1161CutCaps) (weightFloor := vcS1161CutWeightFloor) (margins := vcS1161CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1161Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1161Cut_layer0)
    (by decide +kernel) vcS1161Cut_caps_nonneg vcS1161Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1162CutCell) (roots := vcS1162CutRoots)
    (caps := vcS1162CutCaps) (weightFloor := vcS1162CutWeightFloor) (margins := vcS1162CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1162Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1162Cut_layer0)
    (by decide +kernel) vcS1162Cut_caps_nonneg vcS1162Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1163CutCell) (roots := vcS1163CutRoots)
    (caps := vcS1163CutCaps) (weightFloor := vcS1163CutWeightFloor) (margins := vcS1163CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1163Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1163Cut_layer0)
    (by decide +kernel) vcS1163Cut_caps_nonneg vcS1163Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1164CutCell) (roots := vcS1164CutRoots)
    (caps := vcS1164CutCaps) (weightFloor := vcS1164CutWeightFloor) (margins := vcS1164CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1164Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1164Cut_layer0)
    (by decide +kernel) vcS1164Cut_caps_nonneg vcS1164Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1165CutCell) (roots := vcS1165CutRoots)
    (caps := vcS1165CutCaps) (weightFloor := vcS1165CutWeightFloor) (margins := vcS1165CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1165Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1165Cut_layer0)
    (by decide +kernel) vcS1165Cut_caps_nonneg vcS1165Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1166CutCell) (roots := vcS1166CutRoots)
    (caps := vcS1166CutCaps) (weightFloor := vcS1166CutWeightFloor) (margins := vcS1166CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1166Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1166Cut_layer0)
    (by decide +kernel) vcS1166Cut_caps_nonneg vcS1166Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1167CutCell) (roots := vcS1167CutRoots)
    (caps := vcS1167CutCaps) (weightFloor := vcS1167CutWeightFloor) (margins := vcS1167CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1167Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1167Cut_layer0)
    (by decide +kernel) vcS1167Cut_caps_nonneg vcS1167Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1168CutCell) (roots := vcS1168CutRoots)
    (caps := vcS1168CutCaps) (weightFloor := vcS1168CutWeightFloor) (margins := vcS1168CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1168Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1168Cut_layer0)
    (by decide +kernel) vcS1168Cut_caps_nonneg vcS1168Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1169CutCell) (roots := vcS1169CutRoots)
    (caps := vcS1169CutCaps) (weightFloor := vcS1169CutWeightFloor) (margins := vcS1169CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1169Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1169Cut_layer0)
    (by decide +kernel) vcS1169Cut_caps_nonneg vcS1169Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1170CutCell) (roots := vcS1170CutRoots)
    (caps := vcS1170CutCaps) (weightFloor := vcS1170CutWeightFloor) (margins := vcS1170CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1170Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1170Cut_layer0)
    (by decide +kernel) vcS1170Cut_caps_nonneg vcS1170Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1171CutCell) (roots := vcS1171CutRoots)
    (caps := vcS1171CutCaps) (weightFloor := vcS1171CutWeightFloor) (margins := vcS1171CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1171Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1171Cut_layer0)
    (by decide +kernel) vcS1171Cut_caps_nonneg vcS1171Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1172CutCell) (roots := vcS1172CutRoots)
    (caps := vcS1172CutCaps) (weightFloor := vcS1172CutWeightFloor) (margins := vcS1172CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1172Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1172Cut_layer0)
    (by decide +kernel) vcS1172Cut_caps_nonneg vcS1172Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1173CutCell) (roots := vcS1173CutRoots)
    (caps := vcS1173CutCaps) (weightFloor := vcS1173CutWeightFloor) (margins := vcS1173CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1173Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1173Cut_layer0)
    (by decide +kernel) vcS1173Cut_caps_nonneg vcS1173Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1174CutCell) (roots := vcS1174CutRoots)
    (caps := vcS1174CutCaps) (weightFloor := vcS1174CutWeightFloor) (margins := vcS1174CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1174Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1174Cut_layer0)
    (by decide +kernel) vcS1174Cut_caps_nonneg vcS1174Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1175CutCell) (roots := vcS1175CutRoots)
    (caps := vcS1175CutCaps) (weightFloor := vcS1175CutWeightFloor) (margins := vcS1175CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1175Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1175Cut_layer0)
    (by decide +kernel) vcS1175Cut_caps_nonneg vcS1175Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1176CutCell) (roots := vcS1176CutRoots)
    (caps := vcS1176CutCaps) (weightFloor := vcS1176CutWeightFloor) (margins := vcS1176CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1176Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1176Cut_layer0)
    (by decide +kernel) vcS1176Cut_caps_nonneg vcS1176Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1177CutCell) (roots := vcS1177CutRoots)
    (caps := vcS1177CutCaps) (weightFloor := vcS1177CutWeightFloor) (margins := vcS1177CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1177Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1177Cut_layer0)
    (by decide +kernel) vcS1177Cut_caps_nonneg vcS1177Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1178CutCell) (roots := vcS1178CutRoots)
    (caps := vcS1178CutCaps) (weightFloor := vcS1178CutWeightFloor) (margins := vcS1178CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1178Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1178Cut_layer0)
    (by decide +kernel) vcS1178Cut_caps_nonneg vcS1178Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1179CutCell) (roots := vcS1179CutRoots)
    (caps := vcS1179CutCaps) (weightFloor := vcS1179CutWeightFloor) (margins := vcS1179CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1179Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1179Cut_layer0)
    (by decide +kernel) vcS1179Cut_caps_nonneg vcS1179Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1180CutCell) (roots := vcS1180CutRoots)
    (caps := vcS1180CutCaps) (weightFloor := vcS1180CutWeightFloor) (margins := vcS1180CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1180Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1180Cut_layer0)
    (by decide +kernel) vcS1180Cut_caps_nonneg vcS1180Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1181CutCell) (roots := vcS1181CutRoots)
    (caps := vcS1181CutCaps) (weightFloor := vcS1181CutWeightFloor) (margins := vcS1181CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1181Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1181Cut_layer0)
    (by decide +kernel) vcS1181Cut_caps_nonneg vcS1181Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1182CutCell) (roots := vcS1182CutRoots)
    (caps := vcS1182CutCaps) (weightFloor := vcS1182CutWeightFloor) (margins := vcS1182CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1182Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1182Cut_layer0)
    (by decide +kernel) vcS1182Cut_caps_nonneg vcS1182Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1183CutCell) (roots := vcS1183CutRoots)
    (caps := vcS1183CutCaps) (weightFloor := vcS1183CutWeightFloor) (margins := vcS1183CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1183Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1183Cut_layer0)
    (by decide +kernel) vcS1183Cut_caps_nonneg vcS1183Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1184CutCell) (roots := vcS1184CutRoots)
    (caps := vcS1184CutCaps) (weightFloor := vcS1184CutWeightFloor) (margins := vcS1184CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1184Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1184Cut_layer0)
    (by decide +kernel) vcS1184Cut_caps_nonneg vcS1184Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1185CutCell) (roots := vcS1185CutRoots)
    (caps := vcS1185CutCaps) (weightFloor := vcS1185CutWeightFloor) (margins := vcS1185CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1185Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1185Cut_layer0)
    (by decide +kernel) vcS1185Cut_caps_nonneg vcS1185Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1186CutCell) (roots := vcS1186CutRoots)
    (caps := vcS1186CutCaps) (weightFloor := vcS1186CutWeightFloor) (margins := vcS1186CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1186Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1186Cut_layer0)
    (by decide +kernel) vcS1186Cut_caps_nonneg vcS1186Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1187CutCell) (roots := vcS1187CutRoots)
    (caps := vcS1187CutCaps) (weightFloor := vcS1187CutWeightFloor) (margins := vcS1187CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1187Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1187Cut_layer0)
    (by decide +kernel) vcS1187Cut_caps_nonneg vcS1187Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1188CutCell) (roots := vcS1188CutRoots)
    (caps := vcS1188CutCaps) (weightFloor := vcS1188CutWeightFloor) (margins := vcS1188CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1188Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1188Cut_layer0)
    (by decide +kernel) vcS1188Cut_caps_nonneg vcS1188Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1189CutCell) (roots := vcS1189CutRoots)
    (caps := vcS1189CutCaps) (weightFloor := vcS1189CutWeightFloor) (margins := vcS1189CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1189Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1189Cut_layer0)
    (by decide +kernel) vcS1189Cut_caps_nonneg vcS1189Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1190CutCell) (roots := vcS1190CutRoots)
    (caps := vcS1190CutCaps) (weightFloor := vcS1190CutWeightFloor) (margins := vcS1190CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1190Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1190Cut_layer0)
    (by decide +kernel) vcS1190Cut_caps_nonneg vcS1190Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1191CutCell) (roots := vcS1191CutRoots)
    (caps := vcS1191CutCaps) (weightFloor := vcS1191CutWeightFloor) (margins := vcS1191CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1191Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1191Cut_layer0)
    (by decide +kernel) vcS1191Cut_caps_nonneg vcS1191Cut_margin_le (by decide) (by decide +kernel)]

def vcCutBandCertificates192 : List (CurvatureCellCertificate) := [
  CurvatureCellCertificate.of_layer_checks (c := vcS1192CutCell) (roots := vcS1192CutRoots)
    (caps := vcS1192CutCaps) (weightFloor := vcS1192CutWeightFloor) (margins := vcS1192CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1192Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1192Cut_layer0)
    (by decide +kernel) vcS1192Cut_caps_nonneg vcS1192Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1193CutCell) (roots := vcS1193CutRoots)
    (caps := vcS1193CutCaps) (weightFloor := vcS1193CutWeightFloor) (margins := vcS1193CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1193Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1193Cut_layer0)
    (by decide +kernel) vcS1193Cut_caps_nonneg vcS1193Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1194CutCell) (roots := vcS1194CutRoots)
    (caps := vcS1194CutCaps) (weightFloor := vcS1194CutWeightFloor) (margins := vcS1194CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1194Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1194Cut_layer0)
    (by decide +kernel) vcS1194Cut_caps_nonneg vcS1194Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1195CutCell) (roots := vcS1195CutRoots)
    (caps := vcS1195CutCaps) (weightFloor := vcS1195CutWeightFloor) (margins := vcS1195CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1195Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1195Cut_layer0)
    (by decide +kernel) vcS1195Cut_caps_nonneg vcS1195Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1196CutCell) (roots := vcS1196CutRoots)
    (caps := vcS1196CutCaps) (weightFloor := vcS1196CutWeightFloor) (margins := vcS1196CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1196Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1196Cut_layer0)
    (by decide +kernel) vcS1196Cut_caps_nonneg vcS1196Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1197CutCell) (roots := vcS1197CutRoots)
    (caps := vcS1197CutCaps) (weightFloor := vcS1197CutWeightFloor) (margins := vcS1197CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1197Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1197Cut_layer0)
    (by decide +kernel) vcS1197Cut_caps_nonneg vcS1197Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1198CutCell) (roots := vcS1198CutRoots)
    (caps := vcS1198CutCaps) (weightFloor := vcS1198CutWeightFloor) (margins := vcS1198CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1198Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1198Cut_layer0)
    (by decide +kernel) vcS1198Cut_caps_nonneg vcS1198Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1199CutCell) (roots := vcS1199CutRoots)
    (caps := vcS1199CutCaps) (weightFloor := vcS1199CutWeightFloor) (margins := vcS1199CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1199Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1199Cut_layer0)
    (by decide +kernel) vcS1199Cut_caps_nonneg vcS1199Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1200CutCell) (roots := vcS1200CutRoots)
    (caps := vcS1200CutCaps) (weightFloor := vcS1200CutWeightFloor) (margins := vcS1200CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1200Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1200Cut_layer0)
    (by decide +kernel) vcS1200Cut_caps_nonneg vcS1200Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1201CutCell) (roots := vcS1201CutRoots)
    (caps := vcS1201CutCaps) (weightFloor := vcS1201CutWeightFloor) (margins := vcS1201CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1201Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1201Cut_layer0)
    (by decide +kernel) vcS1201Cut_caps_nonneg vcS1201Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1202CutCell) (roots := vcS1202CutRoots)
    (caps := vcS1202CutCaps) (weightFloor := vcS1202CutWeightFloor) (margins := vcS1202CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1202Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1202Cut_layer0)
    (by decide +kernel) vcS1202Cut_caps_nonneg vcS1202Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1203CutCell) (roots := vcS1203CutRoots)
    (caps := vcS1203CutCaps) (weightFloor := vcS1203CutWeightFloor) (margins := vcS1203CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1203Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1203Cut_layer0)
    (by decide +kernel) vcS1203Cut_caps_nonneg vcS1203Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1204CutCell) (roots := vcS1204CutRoots)
    (caps := vcS1204CutCaps) (weightFloor := vcS1204CutWeightFloor) (margins := vcS1204CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1204Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1204Cut_layer0)
    (by decide +kernel) vcS1204Cut_caps_nonneg vcS1204Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1205CutCell) (roots := vcS1205CutRoots)
    (caps := vcS1205CutCaps) (weightFloor := vcS1205CutWeightFloor) (margins := vcS1205CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1205Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1205Cut_layer0)
    (by decide +kernel) vcS1205Cut_caps_nonneg vcS1205Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1206CutCell) (roots := vcS1206CutRoots)
    (caps := vcS1206CutCaps) (weightFloor := vcS1206CutWeightFloor) (margins := vcS1206CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1206Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1206Cut_layer0)
    (by decide +kernel) vcS1206Cut_caps_nonneg vcS1206Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1207CutCell) (roots := vcS1207CutRoots)
    (caps := vcS1207CutCaps) (weightFloor := vcS1207CutWeightFloor) (margins := vcS1207CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1207Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1207Cut_layer0)
    (by decide +kernel) vcS1207Cut_caps_nonneg vcS1207Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1208CutCell) (roots := vcS1208CutRoots)
    (caps := vcS1208CutCaps) (weightFloor := vcS1208CutWeightFloor) (margins := vcS1208CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1208Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1208Cut_layer0)
    (by decide +kernel) vcS1208Cut_caps_nonneg vcS1208Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1209CutCell) (roots := vcS1209CutRoots)
    (caps := vcS1209CutCaps) (weightFloor := vcS1209CutWeightFloor) (margins := vcS1209CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1209Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1209Cut_layer0)
    (by decide +kernel) vcS1209Cut_caps_nonneg vcS1209Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1210CutCell) (roots := vcS1210CutRoots)
    (caps := vcS1210CutCaps) (weightFloor := vcS1210CutWeightFloor) (margins := vcS1210CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1210Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1210Cut_layer0)
    (by decide +kernel) vcS1210Cut_caps_nonneg vcS1210Cut_margin_le (by decide) (by decide +kernel),
  CurvatureCellCertificate.of_layer_checks (c := vcS1211CutCell) (roots := vcS1211CutRoots)
    (caps := vcS1211CutCaps) (weightFloor := vcS1211CutWeightFloor) (margins := vcS1211CutMargins)
    (na := 1) (nb := 1) (nη := 1)
    vcS1211Cut_roots_ok (by
      intro i
      fin_cases i
      · exact vcS1211Cut_layer0)
    (by decide +kernel) vcS1211Cut_caps_nonneg vcS1211Cut_margin_le (by decide) (by decide +kernel)]

def vcCutBandCertificates : List (CurvatureCellCertificate) :=
  vcCutBandCertificates000 ++
  vcCutBandCertificates032 ++
  vcCutBandCertificates064 ++
  vcCutBandCertificates096 ++
  vcCutBandCertificates128 ++
  vcCutBandCertificates160 ++
  vcCutBandCertificates192

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem vcCutBandCertificates_cells :
    vcCutBandCertificates.map CurvatureCellCertificate.cell = vcBandParameterGrid := by
  decide +kernel

end HlawkaSchatten.BelowExponent.Vertex
