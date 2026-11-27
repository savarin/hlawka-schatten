/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegPart9

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H2Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H2NegBox : Box := ⟨![9/34, 1/20, 0, -8], ![27/68, 7/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid0H2NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid0H2NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid0H2NegPart1Tree) (.cut 2 (5/16) (.cut 2 (7/32) (.cut 3 (0) (.cut 1 (3/50) (CutMid0H2NegPart2Tree) (CutMid0H2NegPart3Tree)) (CutMid0H2NegPart4Tree)) (CutMid0H2NegPart5Tree)) (CutMid0H2NegPart6Tree))) (CutMid0H2NegPart7Tree)) (CutMid0H2NegPart8Tree))) (CutMid0H2NegPart9Tree)

set_option maxRecDepth 16000 in
theorem CutMid0H2Neg_checked : CutMid0H2NegTree.commonOK CutMid0H2NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid0H2NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid0H2NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid0H2NegPart2_checked) (CutMid0H2NegPart3_checked)) (CutMid0H2NegPart4_checked)) (CutMid0H2NegPart5_checked)) (CutMid0H2NegPart6_checked))) (CutMid0H2NegPart7_checked)) (CutMid0H2NegPart8_checked))) (CutMid0H2NegPart9_checked)

end HlawkaSchatten.BelowExponent.G3P
