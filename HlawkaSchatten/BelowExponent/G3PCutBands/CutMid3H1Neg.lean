/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPart21

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H1Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H1NegBox : Box := ⟨![9/68, 11/100, 0, -8], ![9/34, 13/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid3H1NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid3H1NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid3H1NegPart1Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (3/25) (.cut 1 (23/200) (.cut 0 (27/136) (CutMid3H1NegPart2Tree) (CutMid3H1NegPart3Tree)) (CutMid3H1NegPart4Tree)) (.cut 1 (1/8) (CutMid3H1NegPart5Tree) (CutMid3H1NegPart6Tree))) (CutMid3H1NegPart7Tree)) (CutMid3H1NegPart8Tree))) (.cut 2 (5/16) (.cut 3 (0) (.cut 1 (3/25) (.cut 3 (-1/8) (CutMid3H1NegPart9Tree) (.cut 2 (7/32) (CutMid3H1NegPart10Tree) (CutMid3H1NegPart11Tree))) (.cut 3 (-1/8) (CutMid3H1NegPart12Tree) (.cut 0 (27/136) (CutMid3H1NegPart13Tree) (CutMid3H1NegPart14Tree)))) (.cut 3 (1/8) (.cut 1 (3/25) (CutMid3H1NegPart15Tree) (CutMid3H1NegPart16Tree)) (CutMid3H1NegPart17Tree))) (CutMid3H1NegPart18Tree))) (CutMid3H1NegPart19Tree)) (CutMid3H1NegPart20Tree))) (CutMid3H1NegPart21Tree)

set_option maxRecDepth 16000 in
theorem CutMid3H1Neg_checked : CutMid3H1NegTree.commonOK CutMid3H1NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H1NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H1NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H1NegPart2_checked) (CutMid3H1NegPart3_checked)) (CutMid3H1NegPart4_checked)) (CertTree.commonCut_ok (CutMid3H1NegPart5_checked) (CutMid3H1NegPart6_checked))) (CutMid3H1NegPart7_checked)) (CutMid3H1NegPart8_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H1NegPart9_checked) (CertTree.commonCut_ok (CutMid3H1NegPart10_checked) (CutMid3H1NegPart11_checked))) (CertTree.commonCut_ok (CutMid3H1NegPart12_checked) (CertTree.commonCut_ok (CutMid3H1NegPart13_checked) (CutMid3H1NegPart14_checked)))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H1NegPart15_checked) (CutMid3H1NegPart16_checked)) (CutMid3H1NegPart17_checked))) (CutMid3H1NegPart18_checked))) (CutMid3H1NegPart19_checked)) (CutMid3H1NegPart20_checked))) (CutMid3H1NegPart21_checked)

end HlawkaSchatten.BelowExponent.G3P
