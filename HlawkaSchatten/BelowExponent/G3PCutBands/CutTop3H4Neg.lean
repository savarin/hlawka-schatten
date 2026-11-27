/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart28
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart29
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPart30

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H4Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H4NegBox : Box := ⟨![9/34, 9/50, 0, -8], ![45/136, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H4NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop3H4NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H4NegPart1Tree) (.cut 3 (0) (.cut 2 (5/16) (.cut 3 (-1/8) (CutTop3H4NegPart2Tree) (.cut 3 (-1/16) (CutTop3H4NegPart3Tree) (.cut 1 (37/200) (.cut 0 (81/272) (CutTop3H4NegPart4Tree) (CutTop3H4NegPart5Tree)) (.cut 0 (81/272) (CutTop3H4NegPart6Tree) (CutTop3H4NegPart7Tree))))) (.cut 3 (-1/8) (CutTop3H4NegPart8Tree) (.cut 3 (-1/16) (CutTop3H4NegPart9Tree) (.cut 3 (-1/32) (.cut 3 (-3/64) (CutTop3H4NegPart10Tree) (CutTop3H4NegPart11Tree)) (.cut 3 (-1/64) (.cut 0 (81/272) (CutTop3H4NegPart12Tree) (.cut 3 (-3/128) (CutTop3H4NegPart13Tree) (CutTop3H4NegPart14Tree))) (.cut 0 (81/272) (.cut 2 (13/32) (CutTop3H4NegPart15Tree) (CutTop3H4NegPart16Tree)) (.cut 2 (13/32) (CutTop3H4NegPart17Tree) (CutTop3H4NegPart18Tree)))))))) (.cut 2 (5/16) (.cut 3 (1/8) (.cut 3 (1/16) (CutTop3H4NegPart19Tree) (CutTop3H4NegPart20Tree)) (CutTop3H4NegPart21Tree)) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 3 (1/32) (.cut 3 (1/64) (.cut 0 (81/272) (CutTop3H4NegPart22Tree) (CutTop3H4NegPart23Tree)) (CutTop3H4NegPart24Tree)) (CutTop3H4NegPart25Tree)) (CutTop3H4NegPart26Tree)) (CutTop3H4NegPart27Tree))))) (CutTop3H4NegPart28Tree)) (CutTop3H4NegPart29Tree))) (CutTop3H4NegPart30Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H4Neg_checked : CutTop3H4NegTree.commonOK CutTop3H4NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H4NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H4NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H4NegPart2_checked) (CertTree.commonCut_ok (CutTop3H4NegPart3_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H4NegPart4_checked) (CutTop3H4NegPart5_checked)) (CertTree.commonCut_ok (CutTop3H4NegPart6_checked) (CutTop3H4NegPart7_checked))))) (CertTree.commonCut_ok (CutTop3H4NegPart8_checked) (CertTree.commonCut_ok (CutTop3H4NegPart9_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H4NegPart10_checked) (CutTop3H4NegPart11_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H4NegPart12_checked) (CertTree.commonCut_ok (CutTop3H4NegPart13_checked) (CutTop3H4NegPart14_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H4NegPart15_checked) (CutTop3H4NegPart16_checked)) (CertTree.commonCut_ok (CutTop3H4NegPart17_checked) (CutTop3H4NegPart18_checked)))))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H4NegPart19_checked) (CutTop3H4NegPart20_checked)) (CutTop3H4NegPart21_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H4NegPart22_checked) (CutTop3H4NegPart23_checked)) (CutTop3H4NegPart24_checked)) (CutTop3H4NegPart25_checked)) (CutTop3H4NegPart26_checked)) (CutTop3H4NegPart27_checked))))) (CutTop3H4NegPart28_checked)) (CutTop3H4NegPart29_checked))) (CutTop3H4NegPart30_checked)

end HlawkaSchatten.BelowExponent.G3P
