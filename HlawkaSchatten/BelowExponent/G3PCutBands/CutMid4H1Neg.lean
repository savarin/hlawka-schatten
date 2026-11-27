/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPart25

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H1Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H1NegBox : Box := ⟨![9/68, 13/100, 0, -8], ![9/34, 3/20, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid4H1NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid4H1NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid4H1NegPart1Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (7/50) (.cut 1 (27/200) (CutMid4H1NegPart2Tree) (CutMid4H1NegPart3Tree)) (CutMid4H1NegPart4Tree)) (CutMid4H1NegPart5Tree)) (CutMid4H1NegPart6Tree))) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutMid4H1NegPart7Tree) (.cut 1 (7/50) (.cut 0 (27/136) (CutMid4H1NegPart8Tree) (CutMid4H1NegPart9Tree)) (.cut 0 (27/136) (.cut 1 (29/200) (CutMid4H1NegPart10Tree) (CutMid4H1NegPart11Tree)) (.cut 1 (29/200) (CutMid4H1NegPart12Tree) (CutMid4H1NegPart13Tree))))) (.cut 3 (1/8) (.cut 1 (7/50) (CutMid4H1NegPart14Tree) (.cut 0 (27/136) (CutMid4H1NegPart15Tree) (CutMid4H1NegPart16Tree))) (CutMid4H1NegPart17Tree))) (.cut 3 (0) (.cut 3 (-1/8) (CutMid4H1NegPart18Tree) (.cut 2 (13/32) (CutMid4H1NegPart19Tree) (CutMid4H1NegPart20Tree))) (CutMid4H1NegPart21Tree)))) (CutMid4H1NegPart22Tree)) (.cut 2 (1/2) (CutMid4H1NegPart23Tree) (CutMid4H1NegPart24Tree)))) (CutMid4H1NegPart25Tree)

set_option maxRecDepth 16000 in
theorem CutMid4H1Neg_checked : CutMid4H1NegTree.commonOK CutMid4H1NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H1NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H1NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H1NegPart2_checked) (CutMid4H1NegPart3_checked)) (CutMid4H1NegPart4_checked)) (CutMid4H1NegPart5_checked)) (CutMid4H1NegPart6_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H1NegPart7_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H1NegPart8_checked) (CutMid4H1NegPart9_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H1NegPart10_checked) (CutMid4H1NegPart11_checked)) (CertTree.commonCut_ok (CutMid4H1NegPart12_checked) (CutMid4H1NegPart13_checked))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H1NegPart14_checked) (CertTree.commonCut_ok (CutMid4H1NegPart15_checked) (CutMid4H1NegPart16_checked))) (CutMid4H1NegPart17_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H1NegPart18_checked) (CertTree.commonCut_ok (CutMid4H1NegPart19_checked) (CutMid4H1NegPart20_checked))) (CutMid4H1NegPart21_checked)))) (CutMid4H1NegPart22_checked)) (CertTree.commonCut_ok (CutMid4H1NegPart23_checked) (CutMid4H1NegPart24_checked)))) (CutMid4H1NegPart25_checked)

end HlawkaSchatten.BelowExponent.G3P
