/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart28
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegPart29

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H2Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H2NegBox : Box := ⟨![9/34, 13/100, 0, -8], ![27/68, 3/20, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid4H2NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid4H2NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid4H2NegPart1Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (7/50) (.cut 1 (27/200) (CutMid4H2NegPart2Tree) (CutMid4H2NegPart3Tree)) (CutMid4H2NegPart4Tree)) (CutMid4H2NegPart5Tree)) (CutMid4H2NegPart6Tree))) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutMid4H2NegPart7Tree) (.cut 1 (7/50) (.cut 0 (45/136) (CutMid4H2NegPart8Tree) (CutMid4H2NegPart9Tree)) (.cut 0 (45/136) (.cut 1 (29/200) (CutMid4H2NegPart10Tree) (CutMid4H2NegPart11Tree)) (.cut 1 (29/200) (CutMid4H2NegPart12Tree) (CutMid4H2NegPart13Tree))))) (.cut 3 (1/8) (.cut 0 (45/136) (.cut 1 (7/50) (CutMid4H2NegPart14Tree) (CutMid4H2NegPart15Tree)) (.cut 1 (7/50) (CutMid4H2NegPart16Tree) (CutMid4H2NegPart17Tree))) (CutMid4H2NegPart18Tree))) (.cut 3 (0) (.cut 3 (-1/8) (CutMid4H2NegPart19Tree) (.cut 1 (7/50) (CutMid4H2NegPart20Tree) (.cut 0 (45/136) (CutMid4H2NegPart21Tree) (CutMid4H2NegPart22Tree)))) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 3 (1/32) (CutMid4H2NegPart23Tree) (CutMid4H2NegPart24Tree)) (CutMid4H2NegPart25Tree)) (CutMid4H2NegPart26Tree))))) (CutMid4H2NegPart27Tree)) (CutMid4H2NegPart28Tree))) (CutMid4H2NegPart29Tree)

set_option maxRecDepth 16000 in
theorem CutMid4H2Neg_checked : CutMid4H2NegTree.commonOK CutMid4H2NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H2NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H2NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H2NegPart2_checked) (CutMid4H2NegPart3_checked)) (CutMid4H2NegPart4_checked)) (CutMid4H2NegPart5_checked)) (CutMid4H2NegPart6_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H2NegPart7_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H2NegPart8_checked) (CutMid4H2NegPart9_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H2NegPart10_checked) (CutMid4H2NegPart11_checked)) (CertTree.commonCut_ok (CutMid4H2NegPart12_checked) (CutMid4H2NegPart13_checked))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H2NegPart14_checked) (CutMid4H2NegPart15_checked)) (CertTree.commonCut_ok (CutMid4H2NegPart16_checked) (CutMid4H2NegPart17_checked))) (CutMid4H2NegPart18_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H2NegPart19_checked) (CertTree.commonCut_ok (CutMid4H2NegPart20_checked) (CertTree.commonCut_ok (CutMid4H2NegPart21_checked) (CutMid4H2NegPart22_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H2NegPart23_checked) (CutMid4H2NegPart24_checked)) (CutMid4H2NegPart25_checked)) (CutMid4H2NegPart26_checked))))) (CutMid4H2NegPart27_checked)) (CutMid4H2NegPart28_checked))) (CutMid4H2NegPart29_checked)

end HlawkaSchatten.BelowExponent.G3P
