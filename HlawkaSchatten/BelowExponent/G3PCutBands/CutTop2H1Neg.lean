/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegPart14

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H1Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H1NegBox : Box := ⟨![9/136, 17/100, 0, -8], ![9/68, 9/50, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop2H1NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop2H1NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop2H1NegPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop2H1NegPart2Tree) (.cut 3 (-1/16) (CutTop2H1NegPart3Tree) (.cut 1 (7/40) (CutTop2H1NegPart4Tree) (CutTop2H1NegPart5Tree)))) (CutTop2H1NegPart6Tree)) (.cut 3 (0) (.cut 3 (-1/8) (CutTop2H1NegPart7Tree) (.cut 2 (13/32) (.cut 3 (-1/16) (CutTop2H1NegPart8Tree) (CutTop2H1NegPart9Tree)) (CutTop2H1NegPart10Tree))) (CutTop2H1NegPart11Tree)))) (CutTop2H1NegPart12Tree)) (CutTop2H1NegPart13Tree))) (CutTop2H1NegPart14Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H1Neg_checked : CutTop2H1NegTree.commonOK CutTop2H1NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H1NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H1NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H1NegPart2_checked) (CertTree.commonCut_ok (CutTop2H1NegPart3_checked) (CertTree.commonCut_ok (CutTop2H1NegPart4_checked) (CutTop2H1NegPart5_checked)))) (CutTop2H1NegPart6_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H1NegPart7_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H1NegPart8_checked) (CutTop2H1NegPart9_checked)) (CutTop2H1NegPart10_checked))) (CutTop2H1NegPart11_checked)))) (CutTop2H1NegPart12_checked)) (CutTop2H1NegPart13_checked))) (CutTop2H1NegPart14_checked)

end HlawkaSchatten.BelowExponent.G3P
