/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H0NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H0NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H0NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H0NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H0NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H0NegPart5

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H0Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H0NegBox : Box := ⟨![0, 7/100, 0, -8], ![9/68, 9/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid1H0NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid1H0NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid1H0NegPart1Tree) (CutMid1H0NegPart2Tree)) (CutMid1H0NegPart3Tree)) (CutMid1H0NegPart4Tree))) (CutMid1H0NegPart5Tree)

set_option maxRecDepth 16000 in
theorem CutMid1H0Neg_checked : CutMid1H0NegTree.commonOK CutMid1H0NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid1H0NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid1H0NegPart1_checked) (CutMid1H0NegPart2_checked)) (CutMid1H0NegPart3_checked)) (CutMid1H0NegPart4_checked))) (CutMid1H0NegPart5_checked)

end HlawkaSchatten.BelowExponent.G3P
