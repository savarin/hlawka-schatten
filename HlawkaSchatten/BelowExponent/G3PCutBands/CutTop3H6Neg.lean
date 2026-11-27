/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart28
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart29
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart30
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart31
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart32
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart33
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPart34

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H6Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H6NegBox : Box := ⟨![27/68, 9/50, 0, -8], ![63/136, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H6NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop3H6NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H6NegPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (CutTop3H6NegPart2Tree) (.cut 2 (5/16) (.cut 1 (37/200) (.cut 3 (-1/16) (CutTop3H6NegPart3Tree) (CutTop3H6NegPart4Tree)) (.cut 3 (-1/16) (CutTop3H6NegPart5Tree) (.cut 0 (117/272) (CutTop3H6NegPart6Tree) (CutTop3H6NegPart7Tree)))) (.cut 3 (-1/16) (CutTop3H6NegPart8Tree) (.cut 3 (-1/32) (.cut 3 (-3/64) (CutTop3H6NegPart9Tree) (.cut 0 (117/272) (CutTop3H6NegPart10Tree) (CutTop3H6NegPart11Tree))) (.cut 3 (-1/64) (.cut 0 (117/272) (.cut 2 (13/32) (CutTop3H6NegPart12Tree) (CutTop3H6NegPart13Tree)) (CutTop3H6NegPart14Tree)) (.cut 0 (117/272) (.cut 2 (13/32) (CutTop3H6NegPart15Tree) (CutTop3H6NegPart16Tree)) (.cut 2 (13/32) (CutTop3H6NegPart17Tree) (CutTop3H6NegPart18Tree)))))))) (.cut 3 (1/8) (.cut 2 (5/16) (.cut 3 (1/16) (.cut 2 (7/32) (CutTop3H6NegPart19Tree) (.cut 3 (1/32) (CutTop3H6NegPart20Tree) (CutTop3H6NegPart21Tree))) (CutTop3H6NegPart22Tree)) (.cut 3 (1/16) (.cut 3 (1/32) (.cut 2 (13/32) (.cut 3 (1/64) (.cut 0 (117/272) (CutTop3H6NegPart23Tree) (CutTop3H6NegPart24Tree)) (CutTop3H6NegPart25Tree)) (CutTop3H6NegPart26Tree)) (CutTop3H6NegPart27Tree)) (CutTop3H6NegPart28Tree))) (CutTop3H6NegPart29Tree)))) (.cut 2 (3/4) (.cut 3 (0) (CutTop3H6NegPart30Tree) (CutTop3H6NegPart31Tree)) (CutTop3H6NegPart32Tree))) (CutTop3H6NegPart33Tree))) (CutTop3H6NegPart34Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H6Neg_checked : CutTop3H6NegTree.commonOK CutTop3H6NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H6NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H6NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H6NegPart2_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H6NegPart3_checked) (CutTop3H6NegPart4_checked)) (CertTree.commonCut_ok (CutTop3H6NegPart5_checked) (CertTree.commonCut_ok (CutTop3H6NegPart6_checked) (CutTop3H6NegPart7_checked)))) (CertTree.commonCut_ok (CutTop3H6NegPart8_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H6NegPart9_checked) (CertTree.commonCut_ok (CutTop3H6NegPart10_checked) (CutTop3H6NegPart11_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H6NegPart12_checked) (CutTop3H6NegPart13_checked)) (CutTop3H6NegPart14_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H6NegPart15_checked) (CutTop3H6NegPart16_checked)) (CertTree.commonCut_ok (CutTop3H6NegPart17_checked) (CutTop3H6NegPart18_checked)))))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H6NegPart19_checked) (CertTree.commonCut_ok (CutTop3H6NegPart20_checked) (CutTop3H6NegPart21_checked))) (CutTop3H6NegPart22_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H6NegPart23_checked) (CutTop3H6NegPart24_checked)) (CutTop3H6NegPart25_checked)) (CutTop3H6NegPart26_checked)) (CutTop3H6NegPart27_checked)) (CutTop3H6NegPart28_checked))) (CutTop3H6NegPart29_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H6NegPart30_checked) (CutTop3H6NegPart31_checked)) (CutTop3H6NegPart32_checked))) (CutTop3H6NegPart33_checked))) (CutTop3H6NegPart34_checked)

end HlawkaSchatten.BelowExponent.G3P
