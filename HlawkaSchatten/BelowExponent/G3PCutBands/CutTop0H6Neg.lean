/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H6NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H6NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H6NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H6NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H6NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H6NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H6NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H6NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H6NegPart8

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H6Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H6NegBox : Box := ⟨![27/68, 3/20, 0, -8], ![63/136, 4/25, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop0H6NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop0H6NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop0H6NegPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (CutTop0H6NegPart2Tree) (CutTop0H6NegPart3Tree)) (.cut 3 (0) (CutTop0H6NegPart4Tree) (CutTop0H6NegPart5Tree)))) (CutTop0H6NegPart6Tree)) (CutTop0H6NegPart7Tree))) (CutTop0H6NegPart8Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H6Neg_checked : CutTop0H6NegTree.commonOK CutTop0H6NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H6NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H6NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H6NegPart2_checked) (CutTop0H6NegPart3_checked)) (CertTree.commonCut_ok (CutTop0H6NegPart4_checked) (CutTop0H6NegPart5_checked)))) (CutTop0H6NegPart6_checked)) (CutTop0H6NegPart7_checked))) (CutTop0H6NegPart8_checked)

end HlawkaSchatten.BelowExponent.G3P
