/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPart15

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H2Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H2NegBox : Box := ⟨![9/68, 17/100, 0, -8], ![27/136, 9/50, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop2H2NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop2H2NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop2H2NegPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop2H2NegPart2Tree) (.cut 3 (-1/16) (CutTop2H2NegPart3Tree) (.cut 1 (7/40) (CutTop2H2NegPart4Tree) (CutTop2H2NegPart5Tree)))) (CutTop2H2NegPart6Tree)) (.cut 3 (0) (.cut 3 (-1/8) (CutTop2H2NegPart7Tree) (.cut 2 (13/32) (.cut 3 (-1/16) (CutTop2H2NegPart8Tree) (.cut 3 (-1/32) (CutTop2H2NegPart9Tree) (CutTop2H2NegPart10Tree))) (CutTop2H2NegPart11Tree))) (CutTop2H2NegPart12Tree)))) (CutTop2H2NegPart13Tree)) (CutTop2H2NegPart14Tree))) (CutTop2H2NegPart15Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H2Neg_checked : CutTop2H2NegTree.commonOK CutTop2H2NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H2NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H2NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H2NegPart2_checked) (CertTree.commonCut_ok (CutTop2H2NegPart3_checked) (CertTree.commonCut_ok (CutTop2H2NegPart4_checked) (CutTop2H2NegPart5_checked)))) (CutTop2H2NegPart6_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H2NegPart7_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H2NegPart8_checked) (CertTree.commonCut_ok (CutTop2H2NegPart9_checked) (CutTop2H2NegPart10_checked))) (CutTop2H2NegPart11_checked))) (CutTop2H2NegPart12_checked)))) (CutTop2H2NegPart13_checked)) (CutTop2H2NegPart14_checked))) (CutTop2H2NegPart15_checked)

end HlawkaSchatten.BelowExponent.G3P
