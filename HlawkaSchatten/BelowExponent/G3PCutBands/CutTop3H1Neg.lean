/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPart16

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H1Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H1NegBox : Box := ⟨![9/136, 9/50, 0, -8], ![9/68, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H1NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop3H1NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H1NegPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop3H1NegPart2Tree) (.cut 3 (-1/16) (CutTop3H1NegPart3Tree) (.cut 1 (37/200) (CutTop3H1NegPart4Tree) (.cut 0 (27/272) (CutTop3H1NegPart5Tree) (CutTop3H1NegPart6Tree))))) (CutTop3H1NegPart7Tree)) (.cut 3 (0) (.cut 3 (-1/8) (CutTop3H1NegPart8Tree) (.cut 2 (13/32) (.cut 3 (-1/16) (CutTop3H1NegPart9Tree) (.cut 3 (-1/32) (CutTop3H1NegPart10Tree) (CutTop3H1NegPart11Tree))) (CutTop3H1NegPart12Tree))) (CutTop3H1NegPart13Tree)))) (CutTop3H1NegPart14Tree)) (CutTop3H1NegPart15Tree))) (CutTop3H1NegPart16Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H1Neg_checked : CutTop3H1NegTree.commonOK CutTop3H1NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H1NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H1NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H1NegPart2_checked) (CertTree.commonCut_ok (CutTop3H1NegPart3_checked) (CertTree.commonCut_ok (CutTop3H1NegPart4_checked) (CertTree.commonCut_ok (CutTop3H1NegPart5_checked) (CutTop3H1NegPart6_checked))))) (CutTop3H1NegPart7_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H1NegPart8_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H1NegPart9_checked) (CertTree.commonCut_ok (CutTop3H1NegPart10_checked) (CutTop3H1NegPart11_checked))) (CutTop3H1NegPart12_checked))) (CutTop3H1NegPart13_checked)))) (CutTop3H1NegPart14_checked)) (CutTop3H1NegPart15_checked))) (CutTop3H1NegPart16_checked)

end HlawkaSchatten.BelowExponent.G3P
