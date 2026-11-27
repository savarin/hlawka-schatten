/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPart18

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H0Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H0NegBox : Box := ⟨![0, 11/100, 0, -8], ![9/68, 13/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid3H0NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid3H0NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid3H0NegPart1Tree) (.cut 3 (1/8) (.cut 1 (3/25) (.cut 1 (23/200) (CutMid3H0NegPart2Tree) (CutMid3H0NegPart3Tree)) (CutMid3H0NegPart4Tree)) (CutMid3H0NegPart5Tree))) (.cut 2 (5/16) (.cut 3 (0) (.cut 1 (3/25) (.cut 2 (7/32) (.cut 3 (-1/8) (CutMid3H0NegPart6Tree) (.cut 1 (23/200) (CutMid3H0NegPart7Tree) (CutMid3H0NegPart8Tree))) (CutMid3H0NegPart9Tree)) (.cut 3 (-1/8) (CutMid3H0NegPart10Tree) (.cut 2 (7/32) (.cut 1 (1/8) (CutMid3H0NegPart11Tree) (CutMid3H0NegPart12Tree)) (CutMid3H0NegPart13Tree)))) (CutMid3H0NegPart14Tree)) (CutMid3H0NegPart15Tree))) (CutMid3H0NegPart16Tree)) (CutMid3H0NegPart17Tree))) (CutMid3H0NegPart18Tree)

set_option maxRecDepth 16000 in
theorem CutMid3H0Neg_checked : CutMid3H0NegTree.commonOK CutMid3H0NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H0NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H0NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H0NegPart2_checked) (CutMid3H0NegPart3_checked)) (CutMid3H0NegPart4_checked)) (CutMid3H0NegPart5_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H0NegPart6_checked) (CertTree.commonCut_ok (CutMid3H0NegPart7_checked) (CutMid3H0NegPart8_checked))) (CutMid3H0NegPart9_checked)) (CertTree.commonCut_ok (CutMid3H0NegPart10_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H0NegPart11_checked) (CutMid3H0NegPart12_checked)) (CutMid3H0NegPart13_checked)))) (CutMid3H0NegPart14_checked)) (CutMid3H0NegPart15_checked))) (CutMid3H0NegPart16_checked)) (CutMid3H0NegPart17_checked))) (CutMid3H0NegPart18_checked)

end HlawkaSchatten.BelowExponent.G3P
