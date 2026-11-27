/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegPart16

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H7Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H7NegBox : Box := ⟨![63/136, 4/25, 0, -8], ![9/17, 17/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop1H7NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop1H7NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop1H7NegPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (CutTop1H7NegPart2Tree) (.cut 2 (5/16) (.cut 1 (33/200) (CutTop1H7NegPart3Tree) (CutTop1H7NegPart4Tree)) (.cut 3 (-1/16) (CutTop1H7NegPart5Tree) (.cut 3 (-1/32) (CutTop1H7NegPart6Tree) (CutTop1H7NegPart7Tree))))) (.cut 3 (1/8) (.cut 2 (5/16) (.cut 3 (1/16) (CutTop1H7NegPart8Tree) (CutTop1H7NegPart9Tree)) (.cut 3 (1/16) (.cut 3 (1/32) (CutTop1H7NegPart10Tree) (CutTop1H7NegPart11Tree)) (CutTop1H7NegPart12Tree))) (CutTop1H7NegPart13Tree)))) (CutTop1H7NegPart14Tree)) (CutTop1H7NegPart15Tree))) (CutTop1H7NegPart16Tree)

set_option maxRecDepth 16000 in
theorem CutTop1H7Neg_checked : CutTop1H7NegTree.commonOK CutTop1H7NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H7NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H7NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H7NegPart2_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H7NegPart3_checked) (CutTop1H7NegPart4_checked)) (CertTree.commonCut_ok (CutTop1H7NegPart5_checked) (CertTree.commonCut_ok (CutTop1H7NegPart6_checked) (CutTop1H7NegPart7_checked))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H7NegPart8_checked) (CutTop1H7NegPart9_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H7NegPart10_checked) (CutTop1H7NegPart11_checked)) (CutTop1H7NegPart12_checked))) (CutTop1H7NegPart13_checked)))) (CutTop1H7NegPart14_checked)) (CutTop1H7NegPart15_checked))) (CutTop1H7NegPart16_checked)

end HlawkaSchatten.BelowExponent.G3P
