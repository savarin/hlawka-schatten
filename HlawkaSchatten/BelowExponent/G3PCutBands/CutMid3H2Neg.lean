/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPart25

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H2NegBox : Box := ⟨![9/34, 11/100, 0, -8], ![27/68, 13/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid3H2NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid3H2NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid3H2NegPart1Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (3/25) (.cut 1 (23/200) (.cut 0 (45/136) (CutMid3H2NegPart2Tree) (.cut 3 (1/32) (CutMid3H2NegPart3Tree) (CutMid3H2NegPart4Tree))) (.cut 0 (45/136) (CutMid3H2NegPart5Tree) (.cut 3 (1/32) (CutMid3H2NegPart6Tree) (CutMid3H2NegPart7Tree)))) (.cut 1 (1/8) (.cut 0 (45/136) (CutMid3H2NegPart8Tree) (CutMid3H2NegPart9Tree)) (CutMid3H2NegPart10Tree))) (CutMid3H2NegPart11Tree)) (CutMid3H2NegPart12Tree))) (.cut 2 (5/16) (.cut 3 (0) (.cut 1 (3/25) (.cut 3 (-1/8) (CutMid3H2NegPart13Tree) (.cut 0 (45/136) (CutMid3H2NegPart14Tree) (CutMid3H2NegPart15Tree))) (.cut 3 (-1/8) (CutMid3H2NegPart16Tree) (.cut 0 (45/136) (CutMid3H2NegPart17Tree) (CutMid3H2NegPart18Tree)))) (.cut 3 (1/8) (.cut 1 (3/25) (CutMid3H2NegPart19Tree) (CutMid3H2NegPart20Tree)) (CutMid3H2NegPart21Tree))) (CutMid3H2NegPart22Tree))) (CutMid3H2NegPart23Tree)) (CutMid3H2NegPart24Tree))) (CutMid3H2NegPart25Tree)

set_option maxRecDepth 16000 in
theorem CutMid3H2Neg_checked : CutMid3H2NegTree.commonOK CutMid3H2NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H2NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H2NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H2NegPart2_checked) (CertTree.commonCut_ok (CutMid3H2NegPart3_checked) (CutMid3H2NegPart4_checked))) (CertTree.commonCut_ok (CutMid3H2NegPart5_checked) (CertTree.commonCut_ok (CutMid3H2NegPart6_checked) (CutMid3H2NegPart7_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H2NegPart8_checked) (CutMid3H2NegPart9_checked)) (CutMid3H2NegPart10_checked))) (CutMid3H2NegPart11_checked)) (CutMid3H2NegPart12_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H2NegPart13_checked) (CertTree.commonCut_ok (CutMid3H2NegPart14_checked) (CutMid3H2NegPart15_checked))) (CertTree.commonCut_ok (CutMid3H2NegPart16_checked) (CertTree.commonCut_ok (CutMid3H2NegPart17_checked) (CutMid3H2NegPart18_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H2NegPart19_checked) (CutMid3H2NegPart20_checked)) (CutMid3H2NegPart21_checked))) (CutMid3H2NegPart22_checked))) (CutMid3H2NegPart23_checked)) (CutMid3H2NegPart24_checked))) (CutMid3H2NegPart25_checked)

end HlawkaSchatten.BelowExponent.G3P
