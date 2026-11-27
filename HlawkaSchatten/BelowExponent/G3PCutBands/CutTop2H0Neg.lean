/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegPart16

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H0Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H0NegBox : Box := ⟨![0, 17/100, 0, -8], ![9/136, 9/50, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop2H0NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop2H0NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop2H0NegPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop2H0NegPart2Tree) (.cut 3 (-1/16) (CutTop2H0NegPart3Tree) (.cut 1 (7/40) (.cut 0 (9/272) (CutTop2H0NegPart4Tree) (CutTop2H0NegPart5Tree)) (.cut 0 (9/272) (CutTop2H0NegPart6Tree) (CutTop2H0NegPart7Tree))))) (CutTop2H0NegPart8Tree)) (.cut 3 (0) (.cut 3 (-1/8) (CutTop2H0NegPart9Tree) (.cut 2 (13/32) (.cut 3 (-1/16) (CutTop2H0NegPart10Tree) (CutTop2H0NegPart11Tree)) (CutTop2H0NegPart12Tree))) (CutTop2H0NegPart13Tree)))) (CutTop2H0NegPart14Tree)) (CutTop2H0NegPart15Tree))) (CutTop2H0NegPart16Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H0Neg_checked : CutTop2H0NegTree.commonOK CutTop2H0NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H0NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H0NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H0NegPart2_checked) (CertTree.commonCut_ok (CutTop2H0NegPart3_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H0NegPart4_checked) (CutTop2H0NegPart5_checked)) (CertTree.commonCut_ok (CutTop2H0NegPart6_checked) (CutTop2H0NegPart7_checked))))) (CutTop2H0NegPart8_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H0NegPart9_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H0NegPart10_checked) (CutTop2H0NegPart11_checked)) (CutTop2H0NegPart12_checked))) (CutTop2H0NegPart13_checked)))) (CutTop2H0NegPart14_checked)) (CutTop2H0NegPart15_checked))) (CutTop2H0NegPart16_checked)

end HlawkaSchatten.BelowExponent.G3P
