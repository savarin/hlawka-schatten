/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart28
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart29
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart30
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart31
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPart32

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H1Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H1NegBox : Box := ⟨![9/136, 19/100, 0, -8], ![9/68, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H1NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop4H1NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H1NegPart1Tree) (.cut 3 (0) (.cut 2 (5/16) (.cut 3 (-1/8) (CutTop4H1NegPart2Tree) (.cut 3 (-1/16) (CutTop4H1NegPart3Tree) (.cut 1 (39/200) (.cut 0 (27/272) (CutTop4H1NegPart4Tree) (CutTop4H1NegPart5Tree)) (.cut 0 (27/272) (CutTop4H1NegPart6Tree) (CutTop4H1NegPart7Tree))))) (.cut 3 (-1/8) (CutTop4H1NegPart8Tree) (.cut 3 (-1/16) (.cut 3 (-3/32) (CutTop4H1NegPart9Tree) (.cut 2 (13/32) (.cut 0 (27/272) (.cut 3 (-5/64) (CutTop4H1NegPart10Tree) (CutTop4H1NegPart11Tree)) (CutTop4H1NegPart12Tree)) (CutTop4H1NegPart13Tree))) (.cut 3 (-1/32) (.cut 3 (-3/64) (.cut 2 (13/32) (.cut 0 (27/272) (CutTop4H1NegPart14Tree) (CutTop4H1NegPart15Tree)) (CutTop4H1NegPart16Tree)) (.cut 2 (13/32) (.cut 0 (27/272) (CutTop4H1NegPart17Tree) (CutTop4H1NegPart18Tree)) (CutTop4H1NegPart19Tree))) (.cut 3 (-1/64) (.cut 0 (27/272) (CutTop4H1NegPart20Tree) (CutTop4H1NegPart21Tree)) (.cut 0 (27/272) (CutTop4H1NegPart22Tree) (.cut 3 (-1/128) (CutTop4H1NegPart23Tree) (CutTop4H1NegPart24Tree)))))))) (.cut 2 (5/16) (CutTop4H1NegPart25Tree) (CutTop4H1NegPart26Tree)))) (CutTop4H1NegPart27Tree)) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H1NegPart28Tree) (.cut 0 (27/272) (CutTop4H1NegPart29Tree) (CutTop4H1NegPart30Tree))) (CutTop4H1NegPart31Tree)))) (CutTop4H1NegPart32Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H1Neg_checked : CutTop4H1NegTree.commonOK CutTop4H1NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H1NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H1NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H1NegPart2_checked) (CertTree.commonCut_ok (CutTop4H1NegPart3_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H1NegPart4_checked) (CutTop4H1NegPart5_checked)) (CertTree.commonCut_ok (CutTop4H1NegPart6_checked) (CutTop4H1NegPart7_checked))))) (CertTree.commonCut_ok (CutTop4H1NegPart8_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H1NegPart9_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H1NegPart10_checked) (CutTop4H1NegPart11_checked)) (CutTop4H1NegPart12_checked)) (CutTop4H1NegPart13_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H1NegPart14_checked) (CutTop4H1NegPart15_checked)) (CutTop4H1NegPart16_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H1NegPart17_checked) (CutTop4H1NegPart18_checked)) (CutTop4H1NegPart19_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H1NegPart20_checked) (CutTop4H1NegPart21_checked)) (CertTree.commonCut_ok (CutTop4H1NegPart22_checked) (CertTree.commonCut_ok (CutTop4H1NegPart23_checked) (CutTop4H1NegPart24_checked)))))))) (CertTree.commonCut_ok (CutTop4H1NegPart25_checked) (CutTop4H1NegPart26_checked)))) (CutTop4H1NegPart27_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop4H1NegPart28_checked) (CertTree.commonCut_ok (CutTop4H1NegPart29_checked) (CutTop4H1NegPart30_checked))) (CutTop4H1NegPart31_checked)))) (CutTop4H1NegPart32_checked)

end HlawkaSchatten.BelowExponent.G3P
