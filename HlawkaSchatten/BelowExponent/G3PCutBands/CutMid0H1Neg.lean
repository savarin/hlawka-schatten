/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H1NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H1NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H1NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H1NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H1NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H1NegPart5

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H1Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H1NegBox : Box := ⟨![9/68, 1/20, 0, -8], ![9/34, 7/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid0H1NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid0H1NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid0H1NegPart1Tree) (CutMid0H1NegPart2Tree)) (CutMid0H1NegPart3Tree)) (CutMid0H1NegPart4Tree))) (CutMid0H1NegPart5Tree)

set_option maxRecDepth 16000 in
theorem CutMid0H1Neg_checked : CutMid0H1NegTree.geometryOK CutMid0H1NegPowerCache CutMid0H1NegBox false = true := CertTree.geometryCut_ok (CertTree.geometryCut_ok (CutMid0H1NegPart0_checked) (CertTree.geometryCut_ok (CertTree.geometryCut_ok (CertTree.geometryCut_ok (CutMid0H1NegPart1_checked) (CutMid0H1NegPart2_checked)) (CutMid0H1NegPart3_checked)) (CutMid0H1NegPart4_checked))) (CutMid0H1NegPart5_checked)

end HlawkaSchatten.BelowExponent.G3P
