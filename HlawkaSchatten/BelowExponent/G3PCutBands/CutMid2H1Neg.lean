/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPart18

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1NegBox : Box := ⟨![9/68, 9/100, 0, -8], ![9/34, 11/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid2H1NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid2H1NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid2H1NegPart1Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (1/10) (CutMid2H1NegPart2Tree) (.cut 1 (21/200) (.cut 0 (27/136) (CutMid2H1NegPart3Tree) (CutMid2H1NegPart4Tree)) (.cut 0 (27/136) (CutMid2H1NegPart5Tree) (CutMid2H1NegPart6Tree)))) (CutMid2H1NegPart7Tree)) (CutMid2H1NegPart8Tree))) (.cut 2 (5/16) (.cut 3 (0) (.cut 2 (7/32) (.cut 1 (1/10) (.cut 3 (-1/8) (CutMid2H1NegPart9Tree) (.cut 1 (19/200) (CutMid2H1NegPart10Tree) (CutMid2H1NegPart11Tree))) (CutMid2H1NegPart12Tree)) (CutMid2H1NegPart13Tree)) (CutMid2H1NegPart14Tree)) (CutMid2H1NegPart15Tree))) (CutMid2H1NegPart16Tree)) (CutMid2H1NegPart17Tree))) (CutMid2H1NegPart18Tree)

set_option maxRecDepth 16000 in
theorem CutMid2H1Neg_checked : CutMid2H1NegTree.commonOK CutMid2H1NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H1NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H1NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H1NegPart2_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H1NegPart3_checked) (CutMid2H1NegPart4_checked)) (CertTree.commonCut_ok (CutMid2H1NegPart5_checked) (CutMid2H1NegPart6_checked)))) (CutMid2H1NegPart7_checked)) (CutMid2H1NegPart8_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H1NegPart9_checked) (CertTree.commonCut_ok (CutMid2H1NegPart10_checked) (CutMid2H1NegPart11_checked))) (CutMid2H1NegPart12_checked)) (CutMid2H1NegPart13_checked)) (CutMid2H1NegPart14_checked)) (CutMid2H1NegPart15_checked))) (CutMid2H1NegPart16_checked)) (CutMid2H1NegPart17_checked))) (CutMid2H1NegPart18_checked)

end HlawkaSchatten.BelowExponent.G3P
