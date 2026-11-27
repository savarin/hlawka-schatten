/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart28
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart29
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart30
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart31
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart32
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart33
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart34
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart35
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart36
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart37
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPart38

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegBox : Box := ⟨![9/68, 19/100, 0, -8], ![27/136, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H2NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop4H2NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H2NegPart1Tree) (.cut 3 (0) (.cut 2 (5/16) (.cut 3 (-1/8) (CutTop4H2NegPart2Tree) (.cut 3 (-1/16) (CutTop4H2NegPart3Tree) (.cut 1 (39/200) (.cut 0 (45/272) (CutTop4H2NegPart4Tree) (CutTop4H2NegPart5Tree)) (.cut 0 (45/272) (CutTop4H2NegPart6Tree) (.cut 3 (-1/32) (CutTop4H2NegPart7Tree) (CutTop4H2NegPart8Tree)))))) (.cut 3 (-1/8) (CutTop4H2NegPart9Tree) (.cut 3 (-1/16) (.cut 3 (-3/32) (CutTop4H2NegPart10Tree) (.cut 2 (13/32) (.cut 0 (45/272) (CutTop4H2NegPart11Tree) (CutTop4H2NegPart12Tree)) (CutTop4H2NegPart13Tree))) (.cut 3 (-1/32) (.cut 3 (-3/64) (.cut 2 (13/32) (.cut 0 (45/272) (CutTop4H2NegPart14Tree) (CutTop4H2NegPart15Tree)) (CutTop4H2NegPart16Tree)) (.cut 2 (13/32) (.cut 0 (45/272) (CutTop4H2NegPart17Tree) (CutTop4H2NegPart18Tree)) (CutTop4H2NegPart19Tree))) (.cut 3 (-1/64) (.cut 0 (45/272) (CutTop4H2NegPart20Tree) (.cut 3 (-3/128) (CutTop4H2NegPart21Tree) (CutTop4H2NegPart22Tree))) (.cut 0 (45/272) (.cut 3 (-1/128) (CutTop4H2NegPart23Tree) (CutTop4H2NegPart24Tree)) (.cut 3 (-1/128) (.cut 0 (99/544) (CutTop4H2NegPart25Tree) (CutTop4H2NegPart26Tree)) (CutTop4H2NegPart27Tree)))))))) (.cut 2 (5/16) (CutTop4H2NegPart28Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 3 (1/32) (.cut 0 (45/272) (CutTop4H2NegPart29Tree) (CutTop4H2NegPart30Tree)) (CutTop4H2NegPart31Tree)) (CutTop4H2NegPart32Tree)) (CutTop4H2NegPart33Tree))))) (CutTop4H2NegPart34Tree)) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H2NegPart35Tree) (CutTop4H2NegPart36Tree)) (CutTop4H2NegPart37Tree)))) (CutTop4H2NegPart38Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H2Neg_checked : CutTop4H2NegTree.commonOK CutTop4H2NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H2NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H2NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H2NegPart2_checked) (CertTree.commonCut_ok (CutTop4H2NegPart3_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H2NegPart4_checked) (CutTop4H2NegPart5_checked)) (CertTree.commonCut_ok (CutTop4H2NegPart6_checked) (CertTree.commonCut_ok (CutTop4H2NegPart7_checked) (CutTop4H2NegPart8_checked)))))) (CertTree.commonCut_ok (CutTop4H2NegPart9_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H2NegPart10_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H2NegPart11_checked) (CutTop4H2NegPart12_checked)) (CutTop4H2NegPart13_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H2NegPart14_checked) (CutTop4H2NegPart15_checked)) (CutTop4H2NegPart16_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H2NegPart17_checked) (CutTop4H2NegPart18_checked)) (CutTop4H2NegPart19_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H2NegPart20_checked) (CertTree.commonCut_ok (CutTop4H2NegPart21_checked) (CutTop4H2NegPart22_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H2NegPart23_checked) (CutTop4H2NegPart24_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H2NegPart25_checked) (CutTop4H2NegPart26_checked)) (CutTop4H2NegPart27_checked)))))))) (CertTree.commonCut_ok (CutTop4H2NegPart28_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H2NegPart29_checked) (CutTop4H2NegPart30_checked)) (CutTop4H2NegPart31_checked)) (CutTop4H2NegPart32_checked)) (CutTop4H2NegPart33_checked))))) (CutTop4H2NegPart34_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H2NegPart35_checked) (CutTop4H2NegPart36_checked)) (CutTop4H2NegPart37_checked)))) (CutTop4H2NegPart38_checked)

end HlawkaSchatten.BelowExponent.G3P
