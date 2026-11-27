/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegPart11

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H2Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H2NegBox : Box := ⟨![9/68, 4/25, 0, -8], ![27/136, 17/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop1H2NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop1H2NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop1H2NegPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop1H2NegPart2Tree) (.cut 3 (-1/16) (CutTop1H2NegPart3Tree) (.cut 1 (33/200) (CutTop1H2NegPart4Tree) (CutTop1H2NegPart5Tree)))) (CutTop1H2NegPart6Tree)) (.cut 3 (0) (CutTop1H2NegPart7Tree) (CutTop1H2NegPart8Tree)))) (CutTop1H2NegPart9Tree)) (CutTop1H2NegPart10Tree))) (CutTop1H2NegPart11Tree)

set_option maxRecDepth 16000 in
theorem CutTop1H2Neg_checked : CutTop1H2NegTree.commonOK CutTop1H2NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H2NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H2NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H2NegPart2_checked) (CertTree.commonCut_ok (CutTop1H2NegPart3_checked) (CertTree.commonCut_ok (CutTop1H2NegPart4_checked) (CutTop1H2NegPart5_checked)))) (CutTop1H2NegPart6_checked)) (CertTree.commonCut_ok (CutTop1H2NegPart7_checked) (CutTop1H2NegPart8_checked)))) (CutTop1H2NegPart9_checked)) (CutTop1H2NegPart10_checked))) (CutTop1H2NegPart11_checked)

end HlawkaSchatten.BelowExponent.G3P
