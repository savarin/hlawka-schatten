/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegPart12

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H3Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H3NegBox : Box := ⟨![27/68, 1/20, 0, -8], ![9/17, 7/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid0H3NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid0H3NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (.cut 1 (3/50) (CutMid0H3NegPart1Tree) (.cut 1 (13/200) (CutMid0H3NegPart2Tree) (CutMid0H3NegPart3Tree))) (CutMid0H3NegPart4Tree)) (.cut 2 (5/16) (.cut 2 (7/32) (.cut 3 (0) (.cut 1 (3/50) (CutMid0H3NegPart5Tree) (CutMid0H3NegPart6Tree)) (CutMid0H3NegPart7Tree)) (CutMid0H3NegPart8Tree)) (CutMid0H3NegPart9Tree))) (CutMid0H3NegPart10Tree)) (CutMid0H3NegPart11Tree))) (CutMid0H3NegPart12Tree)

set_option maxRecDepth 16000 in
theorem CutMid0H3Neg_checked : CutMid0H3NegTree.commonOK CutMid0H3NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid0H3NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid0H3NegPart1_checked) (CertTree.commonCut_ok (CutMid0H3NegPart2_checked) (CutMid0H3NegPart3_checked))) (CutMid0H3NegPart4_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid0H3NegPart5_checked) (CutMid0H3NegPart6_checked)) (CutMid0H3NegPart7_checked)) (CutMid0H3NegPart8_checked)) (CutMid0H3NegPart9_checked))) (CutMid0H3NegPart10_checked)) (CutMid0H3NegPart11_checked))) (CutMid0H3NegPart12_checked)

end HlawkaSchatten.BelowExponent.G3P
