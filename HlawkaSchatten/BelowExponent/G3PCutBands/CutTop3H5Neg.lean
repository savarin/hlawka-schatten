/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart28
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart29
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart30
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart31
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPart32

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H5Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H5NegBox : Box := ⟨![45/136, 9/50, 0, -8], ![27/68, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H5NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop3H5NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H5NegPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (CutTop3H5NegPart2Tree) (.cut 2 (5/16) (.cut 3 (-1/16) (CutTop3H5NegPart3Tree) (.cut 1 (37/200) (.cut 0 (99/272) (CutTop3H5NegPart4Tree) (CutTop3H5NegPart5Tree)) (.cut 0 (99/272) (CutTop3H5NegPart6Tree) (CutTop3H5NegPart7Tree)))) (.cut 3 (-1/16) (CutTop3H5NegPart8Tree) (.cut 3 (-1/32) (.cut 3 (-3/64) (CutTop3H5NegPart9Tree) (CutTop3H5NegPart10Tree)) (.cut 3 (-1/64) (.cut 0 (99/272) (.cut 2 (13/32) (CutTop3H5NegPart11Tree) (CutTop3H5NegPart12Tree)) (.cut 2 (13/32) (CutTop3H5NegPart13Tree) (CutTop3H5NegPart14Tree))) (.cut 0 (99/272) (.cut 2 (13/32) (CutTop3H5NegPart15Tree) (CutTop3H5NegPart16Tree)) (.cut 2 (13/32) (CutTop3H5NegPart17Tree) (CutTop3H5NegPart18Tree)))))))) (.cut 2 (5/16) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 2 (7/32) (CutTop3H5NegPart19Tree) (CutTop3H5NegPart20Tree)) (CutTop3H5NegPart21Tree)) (CutTop3H5NegPart22Tree)) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 3 (1/32) (.cut 2 (13/32) (.cut 3 (1/64) (.cut 0 (99/272) (CutTop3H5NegPart23Tree) (CutTop3H5NegPart24Tree)) (CutTop3H5NegPart25Tree)) (CutTop3H5NegPart26Tree)) (CutTop3H5NegPart27Tree)) (CutTop3H5NegPart28Tree)) (CutTop3H5NegPart29Tree))))) (CutTop3H5NegPart30Tree)) (CutTop3H5NegPart31Tree))) (CutTop3H5NegPart32Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H5Neg_checked : CutTop3H5NegTree.commonOK CutTop3H5NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H5NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H5NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H5NegPart2_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H5NegPart3_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H5NegPart4_checked) (CutTop3H5NegPart5_checked)) (CertTree.commonCut_ok (CutTop3H5NegPart6_checked) (CutTop3H5NegPart7_checked)))) (CertTree.commonCut_ok (CutTop3H5NegPart8_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H5NegPart9_checked) (CutTop3H5NegPart10_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H5NegPart11_checked) (CutTop3H5NegPart12_checked)) (CertTree.commonCut_ok (CutTop3H5NegPart13_checked) (CutTop3H5NegPart14_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H5NegPart15_checked) (CutTop3H5NegPart16_checked)) (CertTree.commonCut_ok (CutTop3H5NegPart17_checked) (CutTop3H5NegPart18_checked)))))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H5NegPart19_checked) (CutTop3H5NegPart20_checked)) (CutTop3H5NegPart21_checked)) (CutTop3H5NegPart22_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H5NegPart23_checked) (CutTop3H5NegPart24_checked)) (CutTop3H5NegPart25_checked)) (CutTop3H5NegPart26_checked)) (CutTop3H5NegPart27_checked)) (CutTop3H5NegPart28_checked)) (CutTop3H5NegPart29_checked))))) (CutTop3H5NegPart30_checked)) (CutTop3H5NegPart31_checked))) (CutTop3H5NegPart32_checked)

end HlawkaSchatten.BelowExponent.G3P
