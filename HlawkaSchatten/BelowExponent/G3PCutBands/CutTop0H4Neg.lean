/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegPart9

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H4Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H4NegBox : Box := ⟨![9/34, 3/20, 0, -8], ![45/136, 4/25, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop0H4NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop0H4NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop0H4NegPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop0H4NegPart2Tree) (.cut 1 (31/200) (CutTop0H4NegPart3Tree) (CutTop0H4NegPart4Tree))) (CutTop0H4NegPart5Tree)) (CutTop0H4NegPart6Tree))) (CutTop0H4NegPart7Tree)) (CutTop0H4NegPart8Tree))) (CutTop0H4NegPart9Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H4Neg_checked : CutTop0H4NegTree.commonOK CutTop0H4NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H4NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H4NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H4NegPart2_checked) (CertTree.commonCut_ok (CutTop0H4NegPart3_checked) (CutTop0H4NegPart4_checked))) (CutTop0H4NegPart5_checked)) (CutTop0H4NegPart6_checked))) (CutTop0H4NegPart7_checked)) (CutTop0H4NegPart8_checked))) (CutTop0H4NegPart9_checked)

end HlawkaSchatten.BelowExponent.G3P
