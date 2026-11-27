/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPart28

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H7Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H7NegBox : Box := ⟨![63/136, 9/50, 0, -8], ![9/17, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H7NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop3H7NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H7NegPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (CutTop3H7NegPart2Tree) (.cut 3 (-1/16) (CutTop3H7NegPart3Tree) (.cut 2 (5/16) (.cut 1 (37/200) (CutTop3H7NegPart4Tree) (CutTop3H7NegPart5Tree)) (.cut 3 (-1/32) (.cut 3 (-3/64) (CutTop3H7NegPart6Tree) (CutTop3H7NegPart7Tree)) (.cut 0 (135/272) (.cut 3 (-1/64) (CutTop3H7NegPart8Tree) (.cut 2 (13/32) (CutTop3H7NegPart9Tree) (CutTop3H7NegPart10Tree))) (.cut 3 (-1/64) (CutTop3H7NegPart11Tree) (.cut 2 (13/32) (CutTop3H7NegPart12Tree) (CutTop3H7NegPart13Tree)))))))) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 2 (5/16) (.cut 2 (7/32) (CutTop3H7NegPart14Tree) (.cut 3 (1/32) (CutTop3H7NegPart15Tree) (CutTop3H7NegPart16Tree))) (.cut 3 (1/32) (.cut 2 (13/32) (.cut 3 (1/64) (.cut 0 (135/272) (CutTop3H7NegPart17Tree) (CutTop3H7NegPart18Tree)) (CutTop3H7NegPart19Tree)) (CutTop3H7NegPart20Tree)) (CutTop3H7NegPart21Tree))) (CutTop3H7NegPart22Tree)) (CutTop3H7NegPart23Tree)))) (.cut 2 (3/4) (.cut 3 (0) (CutTop3H7NegPart24Tree) (CutTop3H7NegPart25Tree)) (CutTop3H7NegPart26Tree))) (CutTop3H7NegPart27Tree))) (CutTop3H7NegPart28Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H7Neg_checked : CutTop3H7NegTree.commonOK CutTop3H7NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H7NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H7NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H7NegPart2_checked) (CertTree.commonCut_ok (CutTop3H7NegPart3_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H7NegPart4_checked) (CutTop3H7NegPart5_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H7NegPart6_checked) (CutTop3H7NegPart7_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H7NegPart8_checked) (CertTree.commonCut_ok (CutTop3H7NegPart9_checked) (CutTop3H7NegPart10_checked))) (CertTree.commonCut_ok (CutTop3H7NegPart11_checked) (CertTree.commonCut_ok (CutTop3H7NegPart12_checked) (CutTop3H7NegPart13_checked)))))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H7NegPart14_checked) (CertTree.commonCut_ok (CutTop3H7NegPart15_checked) (CutTop3H7NegPart16_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H7NegPart17_checked) (CutTop3H7NegPart18_checked)) (CutTop3H7NegPart19_checked)) (CutTop3H7NegPart20_checked)) (CutTop3H7NegPart21_checked))) (CutTop3H7NegPart22_checked)) (CutTop3H7NegPart23_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H7NegPart24_checked) (CutTop3H7NegPart25_checked)) (CutTop3H7NegPart26_checked))) (CutTop3H7NegPart27_checked))) (CutTop3H7NegPart28_checked)

end HlawkaSchatten.BelowExponent.G3P
