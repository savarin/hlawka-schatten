/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPart12

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H1Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H1NegBox : Box := ⟨![9/68, 7/100, 0, -8], ![9/34, 9/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid1H1NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid1H1NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid1H1NegPart1Tree) (CutMid1H1NegPart2Tree)) (.cut 2 (5/16) (.cut 2 (7/32) (.cut 3 (0) (.cut 1 (2/25) (CutMid1H1NegPart3Tree) (.cut 3 (-1/8) (CutMid1H1NegPart4Tree) (.cut 1 (17/200) (CutMid1H1NegPart5Tree) (CutMid1H1NegPart6Tree)))) (CutMid1H1NegPart7Tree)) (CutMid1H1NegPart8Tree)) (CutMid1H1NegPart9Tree))) (CutMid1H1NegPart10Tree)) (CutMid1H1NegPart11Tree))) (CutMid1H1NegPart12Tree)

set_option maxRecDepth 16000 in
theorem CutMid1H1Neg_checked : CutMid1H1NegTree.commonOK CutMid1H1NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid1H1NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid1H1NegPart1_checked) (CutMid1H1NegPart2_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid1H1NegPart3_checked) (CertTree.commonCut_ok (CutMid1H1NegPart4_checked) (CertTree.commonCut_ok (CutMid1H1NegPart5_checked) (CutMid1H1NegPart6_checked)))) (CutMid1H1NegPart7_checked)) (CutMid1H1NegPart8_checked)) (CutMid1H1NegPart9_checked))) (CutMid1H1NegPart10_checked)) (CutMid1H1NegPart11_checked))) (CutMid1H1NegPart12_checked)

end HlawkaSchatten.BelowExponent.G3P
