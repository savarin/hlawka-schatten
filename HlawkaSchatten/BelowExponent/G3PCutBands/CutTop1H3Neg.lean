/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3NegPart11

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H3Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H3NegBox : Box := ⟨![27/136, 4/25, 0, -8], ![9/34, 17/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop1H3NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop1H3NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop1H3NegPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop1H3NegPart2Tree) (.cut 3 (-1/16) (CutTop1H3NegPart3Tree) (.cut 1 (33/200) (CutTop1H3NegPart4Tree) (CutTop1H3NegPart5Tree)))) (CutTop1H3NegPart6Tree)) (.cut 3 (0) (CutTop1H3NegPart7Tree) (CutTop1H3NegPart8Tree)))) (CutTop1H3NegPart9Tree)) (CutTop1H3NegPart10Tree))) (CutTop1H3NegPart11Tree)

set_option maxRecDepth 16000 in
theorem CutTop1H3Neg_checked : CutTop1H3NegTree.commonOK CutTop1H3NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H3NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H3NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H3NegPart2_checked) (CertTree.commonCut_ok (CutTop1H3NegPart3_checked) (CertTree.commonCut_ok (CutTop1H3NegPart4_checked) (CutTop1H3NegPart5_checked)))) (CutTop1H3NegPart6_checked)) (CertTree.commonCut_ok (CutTop1H3NegPart7_checked) (CutTop1H3NegPart8_checked)))) (CutTop1H3NegPart9_checked)) (CutTop1H3NegPart10_checked))) (CutTop1H3NegPart11_checked)

end HlawkaSchatten.BelowExponent.G3P
