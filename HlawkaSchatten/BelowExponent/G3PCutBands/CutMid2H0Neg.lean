/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPart16

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0NegBox : Box := ⟨![0, 9/100, 0, -8], ![9/68, 11/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid2H0NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid2H0NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid2H0NegPart1Tree) (.cut 3 (1/8) (.cut 1 (1/10) (CutMid2H0NegPart2Tree) (.cut 1 (21/200) (CutMid2H0NegPart3Tree) (.cut 0 (9/136) (CutMid2H0NegPart4Tree) (CutMid2H0NegPart5Tree)))) (CutMid2H0NegPart6Tree))) (.cut 2 (5/16) (.cut 3 (0) (.cut 2 (7/32) (.cut 1 (1/10) (CutMid2H0NegPart7Tree) (.cut 3 (-1/8) (CutMid2H0NegPart8Tree) (.cut 1 (21/200) (CutMid2H0NegPart9Tree) (CutMid2H0NegPart10Tree)))) (CutMid2H0NegPart11Tree)) (CutMid2H0NegPart12Tree)) (CutMid2H0NegPart13Tree))) (CutMid2H0NegPart14Tree)) (CutMid2H0NegPart15Tree))) (CutMid2H0NegPart16Tree)

set_option maxRecDepth 16000 in
theorem CutMid2H0Neg_checked : CutMid2H0NegTree.commonOK CutMid2H0NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H0NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H0NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H0NegPart2_checked) (CertTree.commonCut_ok (CutMid2H0NegPart3_checked) (CertTree.commonCut_ok (CutMid2H0NegPart4_checked) (CutMid2H0NegPart5_checked)))) (CutMid2H0NegPart6_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid2H0NegPart7_checked) (CertTree.commonCut_ok (CutMid2H0NegPart8_checked) (CertTree.commonCut_ok (CutMid2H0NegPart9_checked) (CutMid2H0NegPart10_checked)))) (CutMid2H0NegPart11_checked)) (CutMid2H0NegPart12_checked)) (CutMid2H0NegPart13_checked))) (CutMid2H0NegPart14_checked)) (CutMid2H0NegPart15_checked))) (CutMid2H0NegPart16_checked)

end HlawkaSchatten.BelowExponent.G3P
