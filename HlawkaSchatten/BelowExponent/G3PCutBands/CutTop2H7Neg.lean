/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPart19

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H7Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H7NegBox : Box := ⟨![63/136, 17/100, 0, -8], ![9/17, 9/50, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop2H7NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop2H7NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop2H7NegPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (CutTop2H7NegPart2Tree) (.cut 2 (5/16) (.cut 1 (7/40) (CutTop2H7NegPart3Tree) (CutTop2H7NegPart4Tree)) (.cut 3 (-1/16) (CutTop2H7NegPart5Tree) (.cut 3 (-1/32) (CutTop2H7NegPart6Tree) (.cut 0 (135/272) (CutTop2H7NegPart7Tree) (CutTop2H7NegPart8Tree)))))) (.cut 3 (1/8) (.cut 2 (5/16) (.cut 3 (1/16) (.cut 2 (7/32) (CutTop2H7NegPart9Tree) (CutTop2H7NegPart10Tree)) (CutTop2H7NegPart11Tree)) (.cut 3 (1/16) (.cut 3 (1/32) (.cut 2 (13/32) (CutTop2H7NegPart12Tree) (CutTop2H7NegPart13Tree)) (CutTop2H7NegPart14Tree)) (CutTop2H7NegPart15Tree))) (CutTop2H7NegPart16Tree)))) (CutTop2H7NegPart17Tree)) (CutTop2H7NegPart18Tree))) (CutTop2H7NegPart19Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H7Neg_checked : CutTop2H7NegTree.commonOK CutTop2H7NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H7NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H7NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H7NegPart2_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H7NegPart3_checked) (CutTop2H7NegPart4_checked)) (CertTree.commonCut_ok (CutTop2H7NegPart5_checked) (CertTree.commonCut_ok (CutTop2H7NegPart6_checked) (CertTree.commonCut_ok (CutTop2H7NegPart7_checked) (CutTop2H7NegPart8_checked)))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H7NegPart9_checked) (CutTop2H7NegPart10_checked)) (CutTop2H7NegPart11_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H7NegPart12_checked) (CutTop2H7NegPart13_checked)) (CutTop2H7NegPart14_checked)) (CutTop2H7NegPart15_checked))) (CutTop2H7NegPart16_checked)))) (CutTop2H7NegPart17_checked)) (CutTop2H7NegPart18_checked))) (CutTop2H7NegPart19_checked)

end HlawkaSchatten.BelowExponent.G3P
