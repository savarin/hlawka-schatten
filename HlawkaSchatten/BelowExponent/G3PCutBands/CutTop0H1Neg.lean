/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H1NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H1NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H1NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H1NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H1NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H1NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H1NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H1NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H1NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H1NegPart9

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H1Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H1NegBox : Box := ⟨![9/136, 3/20, 0, -8], ![9/68, 4/25, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop0H1NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop0H1NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop0H1NegPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop0H1NegPart2Tree) (.cut 3 (-1/16) (CutTop0H1NegPart3Tree) (CutTop0H1NegPart4Tree))) (CutTop0H1NegPart5Tree)) (CutTop0H1NegPart6Tree))) (CutTop0H1NegPart7Tree)) (CutTop0H1NegPart8Tree))) (CutTop0H1NegPart9Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H1Neg_checked : CutTop0H1NegTree.commonOK CutTop0H1NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H1NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H1NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H1NegPart2_checked) (CertTree.commonCut_ok (CutTop0H1NegPart3_checked) (CutTop0H1NegPart4_checked))) (CutTop0H1NegPart5_checked)) (CutTop0H1NegPart6_checked))) (CutTop0H1NegPart7_checked)) (CutTop0H1NegPart8_checked))) (CutTop0H1NegPart9_checked)

end HlawkaSchatten.BelowExponent.G3P
