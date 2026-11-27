/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPart25

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H0Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H0NegBox : Box := ⟨![0, 13/100, 0, -8], ![9/68, 3/20, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid4H0NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid4H0NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid4H0NegPart1Tree) (.cut 3 (1/8) (.cut 1 (7/50) (CutMid4H0NegPart2Tree) (CutMid4H0NegPart3Tree)) (CutMid4H0NegPart4Tree))) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutMid4H0NegPart5Tree) (.cut 1 (7/50) (.cut 0 (9/136) (.cut 2 (7/32) (.cut 1 (27/200) (CutMid4H0NegPart6Tree) (CutMid4H0NegPart7Tree)) (CutMid4H0NegPart8Tree)) (.cut 2 (7/32) (CutMid4H0NegPart9Tree) (CutMid4H0NegPart10Tree))) (.cut 0 (9/136) (.cut 2 (7/32) (.cut 1 (29/200) (CutMid4H0NegPart11Tree) (CutMid4H0NegPart12Tree)) (CutMid4H0NegPart13Tree)) (.cut 1 (29/200) (CutMid4H0NegPart14Tree) (CutMid4H0NegPart15Tree))))) (.cut 3 (1/8) (CutMid4H0NegPart16Tree) (CutMid4H0NegPart17Tree))) (.cut 3 (0) (.cut 3 (-1/8) (CutMid4H0NegPart18Tree) (CutMid4H0NegPart19Tree)) (CutMid4H0NegPart20Tree)))) (CutMid4H0NegPart21Tree)) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid4H0NegPart22Tree) (CutMid4H0NegPart23Tree)) (CutMid4H0NegPart24Tree)))) (CutMid4H0NegPart25Tree)

set_option maxRecDepth 16000 in
theorem CutMid4H0Neg_checked : CutMid4H0NegTree.commonOK CutMid4H0NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H0NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H0NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H0NegPart2_checked) (CutMid4H0NegPart3_checked)) (CutMid4H0NegPart4_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H0NegPart5_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H0NegPart6_checked) (CutMid4H0NegPart7_checked)) (CutMid4H0NegPart8_checked)) (CertTree.commonCut_ok (CutMid4H0NegPart9_checked) (CutMid4H0NegPart10_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H0NegPart11_checked) (CutMid4H0NegPart12_checked)) (CutMid4H0NegPart13_checked)) (CertTree.commonCut_ok (CutMid4H0NegPart14_checked) (CutMid4H0NegPart15_checked))))) (CertTree.commonCut_ok (CutMid4H0NegPart16_checked) (CutMid4H0NegPart17_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H0NegPart18_checked) (CutMid4H0NegPart19_checked)) (CutMid4H0NegPart20_checked)))) (CutMid4H0NegPart21_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H0NegPart22_checked) (CutMid4H0NegPart23_checked)) (CutMid4H0NegPart24_checked)))) (CutMid4H0NegPart25_checked)

end HlawkaSchatten.BelowExponent.G3P
