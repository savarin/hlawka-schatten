/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegPart10

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H2Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H2NegBox : Box := ⟨![9/68, 3/20, 0, -8], ![27/136, 4/25, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop0H2NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop0H2NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop0H2NegPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop0H2NegPart2Tree) (.cut 3 (-1/16) (CutTop0H2NegPart3Tree) (.cut 1 (31/200) (CutTop0H2NegPart4Tree) (CutTop0H2NegPart5Tree)))) (CutTop0H2NegPart6Tree)) (CutTop0H2NegPart7Tree))) (CutTop0H2NegPart8Tree)) (CutTop0H2NegPart9Tree))) (CutTop0H2NegPart10Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H2Neg_checked : CutTop0H2NegTree.commonOK CutTop0H2NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H2NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H2NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H2NegPart2_checked) (CertTree.commonCut_ok (CutTop0H2NegPart3_checked) (CertTree.commonCut_ok (CutTop0H2NegPart4_checked) (CutTop0H2NegPart5_checked)))) (CutTop0H2NegPart6_checked)) (CutTop0H2NegPart7_checked))) (CutTop0H2NegPart8_checked)) (CutTop0H2NegPart9_checked))) (CutTop0H2NegPart10_checked)

end HlawkaSchatten.BelowExponent.G3P
