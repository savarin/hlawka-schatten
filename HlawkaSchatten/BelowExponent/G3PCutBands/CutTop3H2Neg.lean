/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPart18

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H2Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H2NegBox : Box := ⟨![9/68, 9/50, 0, -8], ![27/136, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H2NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop3H2NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H2NegPart1Tree) (.cut 3 (0) (.cut 2 (5/16) (.cut 3 (-1/8) (CutTop3H2NegPart2Tree) (.cut 3 (-1/16) (CutTop3H2NegPart3Tree) (.cut 1 (37/200) (.cut 0 (45/272) (CutTop3H2NegPart4Tree) (CutTop3H2NegPart5Tree)) (.cut 0 (45/272) (CutTop3H2NegPart6Tree) (CutTop3H2NegPart7Tree))))) (.cut 3 (-1/8) (CutTop3H2NegPart8Tree) (.cut 3 (-1/16) (CutTop3H2NegPart9Tree) (.cut 3 (-1/32) (CutTop3H2NegPart10Tree) (.cut 3 (-1/64) (CutTop3H2NegPart11Tree) (.cut 0 (45/272) (CutTop3H2NegPart12Tree) (CutTop3H2NegPart13Tree))))))) (.cut 2 (5/16) (CutTop3H2NegPart14Tree) (CutTop3H2NegPart15Tree)))) (CutTop3H2NegPart16Tree)) (CutTop3H2NegPart17Tree))) (CutTop3H2NegPart18Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H2Neg_checked : CutTop3H2NegTree.commonOK CutTop3H2NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H2NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H2NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H2NegPart2_checked) (CertTree.commonCut_ok (CutTop3H2NegPart3_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H2NegPart4_checked) (CutTop3H2NegPart5_checked)) (CertTree.commonCut_ok (CutTop3H2NegPart6_checked) (CutTop3H2NegPart7_checked))))) (CertTree.commonCut_ok (CutTop3H2NegPart8_checked) (CertTree.commonCut_ok (CutTop3H2NegPart9_checked) (CertTree.commonCut_ok (CutTop3H2NegPart10_checked) (CertTree.commonCut_ok (CutTop3H2NegPart11_checked) (CertTree.commonCut_ok (CutTop3H2NegPart12_checked) (CutTop3H2NegPart13_checked))))))) (CertTree.commonCut_ok (CutTop3H2NegPart14_checked) (CutTop3H2NegPart15_checked)))) (CutTop3H2NegPart16_checked)) (CutTop3H2NegPart17_checked))) (CutTop3H2NegPart18_checked)

end HlawkaSchatten.BelowExponent.G3P
