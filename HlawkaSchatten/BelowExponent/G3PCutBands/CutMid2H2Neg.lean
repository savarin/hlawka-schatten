/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPart24

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H2Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H2NegBox : Box := ⟨![9/34, 9/100, 0, -8], ![27/68, 11/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid2H2NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid2H2NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid2H2NegPart1Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (1/10) (.cut 1 (19/200) (CutMid2H2NegPart2Tree) (.cut 0 (45/136) (CutMid2H2NegPart3Tree) (.cut 1 (39/400) (CutMid2H2NegPart4Tree) (CutMid2H2NegPart5Tree)))) (.cut 1 (21/200) (.cut 0 (45/136) (.cut 1 (41/400) (CutMid2H2NegPart6Tree) (CutMid2H2NegPart7Tree)) (.cut 3 (1/32) (CutMid2H2NegPart8Tree) (CutMid2H2NegPart9Tree))) (.cut 0 (45/136) (.cut 1 (43/400) (CutMid2H2NegPart10Tree) (CutMid2H2NegPart11Tree)) (.cut 3 (1/32) (CutMid2H2NegPart12Tree) (CutMid2H2NegPart13Tree))))) (CutMid2H2NegPart14Tree)) (CutMid2H2NegPart15Tree))) (.cut 2 (5/16) (.cut 3 (0) (.cut 1 (1/10) (.cut 2 (7/32) (CutMid2H2NegPart16Tree) (CutMid2H2NegPart17Tree)) (CutMid2H2NegPart18Tree)) (.cut 3 (1/8) (CutMid2H2NegPart19Tree) (CutMid2H2NegPart20Tree))) (CutMid2H2NegPart21Tree))) (CutMid2H2NegPart22Tree)) (CutMid2H2NegPart23Tree))) (CutMid2H2NegPart24Tree)

set_option maxRecDepth 16000 in
theorem CutMid2H2Neg_checked : CutMid2H2NegTree.commonOK CutMid2H2NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H2NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H2NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H2NegPart2_checked) (CertTree.commonCut_ok (CutMid2H2NegPart3_checked) (CertTree.commonCut_ok (CutMid2H2NegPart4_checked) (CutMid2H2NegPart5_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H2NegPart6_checked) (CutMid2H2NegPart7_checked)) (CertTree.commonCut_ok (CutMid2H2NegPart8_checked) (CutMid2H2NegPart9_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H2NegPart10_checked) (CutMid2H2NegPart11_checked)) (CertTree.commonCut_ok (CutMid2H2NegPart12_checked) (CutMid2H2NegPart13_checked))))) (CutMid2H2NegPart14_checked)) (CutMid2H2NegPart15_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H2NegPart16_checked) (CutMid2H2NegPart17_checked)) (CutMid2H2NegPart18_checked)) (CertTree.commonCut_ok (CutMid2H2NegPart19_checked) (CutMid2H2NegPart20_checked))) (CutMid2H2NegPart21_checked))) (CutMid2H2NegPart22_checked)) (CutMid2H2NegPart23_checked))) (CutMid2H2NegPart24_checked)

end HlawkaSchatten.BelowExponent.G3P
