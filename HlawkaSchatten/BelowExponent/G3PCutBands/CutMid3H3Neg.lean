/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPart23

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3NegBox : Box := ⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid3H3NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid3H3NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid3H3NegPart1Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (3/25) (.cut 3 (1/32) (.cut 1 (23/200) (CutMid3H3NegPart2Tree) (CutMid3H3NegPart3Tree)) (CutMid3H3NegPart4Tree)) (CutMid3H3NegPart5Tree)) (CutMid3H3NegPart6Tree)) (CutMid3H3NegPart7Tree))) (.cut 2 (5/16) (.cut 3 (0) (.cut 1 (3/25) (.cut 3 (-1/8) (CutMid3H3NegPart8Tree) (.cut 0 (63/136) (CutMid3H3NegPart9Tree) (CutMid3H3NegPart10Tree))) (.cut 3 (-1/8) (CutMid3H3NegPart11Tree) (.cut 0 (63/136) (CutMid3H3NegPart12Tree) (CutMid3H3NegPart13Tree)))) (.cut 3 (1/8) (.cut 1 (3/25) (.cut 0 (63/136) (CutMid3H3NegPart14Tree) (CutMid3H3NegPart15Tree)) (.cut 0 (63/136) (CutMid3H3NegPart16Tree) (CutMid3H3NegPart17Tree))) (CutMid3H3NegPart18Tree))) (.cut 3 (0) (CutMid3H3NegPart19Tree) (CutMid3H3NegPart20Tree)))) (CutMid3H3NegPart21Tree)) (CutMid3H3NegPart22Tree))) (CutMid3H3NegPart23Tree)

set_option maxRecDepth 16000 in
theorem CutMid3H3Neg_checked : CutMid3H3NegTree.commonOK CutMid3H3NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H3NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H3NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H3NegPart2_checked) (CutMid3H3NegPart3_checked)) (CutMid3H3NegPart4_checked)) (CutMid3H3NegPart5_checked)) (CutMid3H3NegPart6_checked)) (CutMid3H3NegPart7_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H3NegPart8_checked) (CertTree.commonCut_ok (CutMid3H3NegPart9_checked) (CutMid3H3NegPart10_checked))) (CertTree.commonCut_ok (CutMid3H3NegPart11_checked) (CertTree.commonCut_ok (CutMid3H3NegPart12_checked) (CutMid3H3NegPart13_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H3NegPart14_checked) (CutMid3H3NegPart15_checked)) (CertTree.commonCut_ok (CutMid3H3NegPart16_checked) (CutMid3H3NegPart17_checked))) (CutMid3H3NegPart18_checked))) (CertTree.commonCut_ok (CutMid3H3NegPart19_checked) (CutMid3H3NegPart20_checked)))) (CutMid3H3NegPart21_checked)) (CutMid3H3NegPart22_checked))) (CutMid3H3NegPart23_checked)

end HlawkaSchatten.BelowExponent.G3P
