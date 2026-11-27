/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPart16

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H2Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H2NegBox : Box := ⟨![9/34, 7/100, 0, -8], ![27/68, 9/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid1H2NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid1H2NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (.cut 1 (2/25) (CutMid1H2NegPart1Tree) (CutMid1H2NegPart2Tree)) (.cut 3 (1/8) (.cut 3 (1/16) (CutMid1H2NegPart3Tree) (CutMid1H2NegPart4Tree)) (CutMid1H2NegPart5Tree))) (.cut 2 (5/16) (.cut 2 (7/32) (.cut 3 (0) (.cut 1 (2/25) (.cut 1 (3/40) (CutMid1H2NegPart6Tree) (CutMid1H2NegPart7Tree)) (.cut 3 (-1/8) (CutMid1H2NegPart8Tree) (.cut 1 (17/200) (CutMid1H2NegPart9Tree) (CutMid1H2NegPart10Tree)))) (CutMid1H2NegPart11Tree)) (CutMid1H2NegPart12Tree)) (CutMid1H2NegPart13Tree))) (CutMid1H2NegPart14Tree)) (CutMid1H2NegPart15Tree))) (CutMid1H2NegPart16Tree)

set_option maxRecDepth 16000 in
theorem CutMid1H2Neg_checked : CutMid1H2NegTree.commonOK CutMid1H2NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid1H2NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid1H2NegPart1_checked) (CutMid1H2NegPart2_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid1H2NegPart3_checked) (CutMid1H2NegPart4_checked)) (CutMid1H2NegPart5_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid1H2NegPart6_checked) (CutMid1H2NegPart7_checked)) (CertTree.commonCut_ok (CutMid1H2NegPart8_checked) (CertTree.commonCut_ok (CutMid1H2NegPart9_checked) (CutMid1H2NegPart10_checked)))) (CutMid1H2NegPart11_checked)) (CutMid1H2NegPart12_checked)) (CutMid1H2NegPart13_checked))) (CutMid1H2NegPart14_checked)) (CutMid1H2NegPart15_checked))) (CutMid1H2NegPart16_checked)

end HlawkaSchatten.BelowExponent.G3P
