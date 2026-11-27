/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegPart10

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H0Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H0NegBox : Box := ⟨![0, 3/20, 0, -8], ![9/136, 4/25, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop0H0NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop0H0NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop0H0NegPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop0H0NegPart2Tree) (.cut 3 (-1/16) (CutTop0H0NegPart3Tree) (.cut 1 (31/200) (CutTop0H0NegPart4Tree) (CutTop0H0NegPart5Tree)))) (CutTop0H0NegPart6Tree)) (CutTop0H0NegPart7Tree))) (CutTop0H0NegPart8Tree)) (CutTop0H0NegPart9Tree))) (CutTop0H0NegPart10Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H0Neg_checked : CutTop0H0NegTree.commonOK CutTop0H0NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H0NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H0NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H0NegPart2_checked) (CertTree.commonCut_ok (CutTop0H0NegPart3_checked) (CertTree.commonCut_ok (CutTop0H0NegPart4_checked) (CutTop0H0NegPart5_checked)))) (CutTop0H0NegPart6_checked)) (CutTop0H0NegPart7_checked))) (CutTop0H0NegPart8_checked)) (CutTop0H0NegPart9_checked))) (CutTop0H0NegPart10_checked)

end HlawkaSchatten.BelowExponent.G3P
