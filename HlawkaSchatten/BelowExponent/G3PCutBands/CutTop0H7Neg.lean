/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegPart9

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H7Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H7NegBox : Box := ⟨![63/136, 3/20, 0, -8], ![9/17, 4/25, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop0H7NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop0H7NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop0H7NegPart1Tree) (.cut 3 (0) (.cut 2 (5/16) (CutTop0H7NegPart2Tree) (CutTop0H7NegPart3Tree)) (.cut 2 (5/16) (.cut 3 (1/8) (CutTop0H7NegPart4Tree) (CutTop0H7NegPart5Tree)) (CutTop0H7NegPart6Tree)))) (CutTop0H7NegPart7Tree)) (CutTop0H7NegPart8Tree))) (CutTop0H7NegPart9Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H7Neg_checked : CutTop0H7NegTree.commonOK CutTop0H7NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H7NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H7NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H7NegPart2_checked) (CutTop0H7NegPart3_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H7NegPart4_checked) (CutTop0H7NegPart5_checked)) (CutTop0H7NegPart6_checked)))) (CutTop0H7NegPart7_checked)) (CutTop0H7NegPart8_checked))) (CutTop0H7NegPart9_checked)

end HlawkaSchatten.BelowExponent.G3P
