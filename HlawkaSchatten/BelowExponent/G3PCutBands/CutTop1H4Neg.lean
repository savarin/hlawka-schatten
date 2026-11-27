/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegPart13

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H4Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H4NegBox : Box := ⟨![9/34, 4/25, 0, -8], ![45/136, 17/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop1H4NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop1H4NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop1H4NegPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop1H4NegPart2Tree) (.cut 3 (-1/16) (CutTop1H4NegPart3Tree) (.cut 1 (33/200) (CutTop1H4NegPart4Tree) (CutTop1H4NegPart5Tree)))) (CutTop1H4NegPart6Tree)) (.cut 3 (0) (.cut 3 (-1/8) (CutTop1H4NegPart7Tree) (.cut 2 (13/32) (CutTop1H4NegPart8Tree) (CutTop1H4NegPart9Tree))) (CutTop1H4NegPart10Tree)))) (CutTop1H4NegPart11Tree)) (CutTop1H4NegPart12Tree))) (CutTop1H4NegPart13Tree)

set_option maxRecDepth 16000 in
theorem CutTop1H4Neg_checked : CutTop1H4NegTree.commonOK CutTop1H4NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H4NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H4NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H4NegPart2_checked) (CertTree.commonCut_ok (CutTop1H4NegPart3_checked) (CertTree.commonCut_ok (CutTop1H4NegPart4_checked) (CutTop1H4NegPart5_checked)))) (CutTop1H4NegPart6_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H4NegPart7_checked) (CertTree.commonCut_ok (CutTop1H4NegPart8_checked) (CutTop1H4NegPart9_checked))) (CutTop1H4NegPart10_checked)))) (CutTop1H4NegPart11_checked)) (CutTop1H4NegPart12_checked))) (CutTop1H4NegPart13_checked)

end HlawkaSchatten.BelowExponent.G3P
