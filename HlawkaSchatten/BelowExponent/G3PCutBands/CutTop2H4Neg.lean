/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPart22

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H4Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H4NegBox : Box := ⟨![9/34, 17/100, 0, -8], ![45/136, 9/50, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop2H4NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop2H4NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop2H4NegPart1Tree) (.cut 3 (0) (.cut 2 (5/16) (.cut 3 (-1/8) (CutTop2H4NegPart2Tree) (.cut 3 (-1/16) (CutTop2H4NegPart3Tree) (.cut 1 (7/40) (.cut 0 (81/272) (CutTop2H4NegPart4Tree) (CutTop2H4NegPart5Tree)) (.cut 0 (81/272) (CutTop2H4NegPart6Tree) (CutTop2H4NegPart7Tree))))) (.cut 3 (-1/8) (CutTop2H4NegPart8Tree) (.cut 3 (-1/16) (CutTop2H4NegPart9Tree) (.cut 3 (-1/32) (CutTop2H4NegPart10Tree) (.cut 3 (-1/64) (CutTop2H4NegPart11Tree) (.cut 0 (81/272) (CutTop2H4NegPart12Tree) (CutTop2H4NegPart13Tree))))))) (.cut 2 (5/16) (.cut 3 (1/8) (CutTop2H4NegPart14Tree) (CutTop2H4NegPart15Tree)) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 3 (1/32) (CutTop2H4NegPart16Tree) (CutTop2H4NegPart17Tree)) (CutTop2H4NegPart18Tree)) (CutTop2H4NegPart19Tree))))) (CutTop2H4NegPart20Tree)) (CutTop2H4NegPart21Tree))) (CutTop2H4NegPart22Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H4Neg_checked : CutTop2H4NegTree.commonOK CutTop2H4NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H4NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H4NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H4NegPart2_checked) (CertTree.commonCut_ok (CutTop2H4NegPart3_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H4NegPart4_checked) (CutTop2H4NegPart5_checked)) (CertTree.commonCut_ok (CutTop2H4NegPart6_checked) (CutTop2H4NegPart7_checked))))) (CertTree.commonCut_ok (CutTop2H4NegPart8_checked) (CertTree.commonCut_ok (CutTop2H4NegPart9_checked) (CertTree.commonCut_ok (CutTop2H4NegPart10_checked) (CertTree.commonCut_ok (CutTop2H4NegPart11_checked) (CertTree.commonCut_ok (CutTop2H4NegPart12_checked) (CutTop2H4NegPart13_checked))))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H4NegPart14_checked) (CutTop2H4NegPart15_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H4NegPart16_checked) (CutTop2H4NegPart17_checked)) (CutTop2H4NegPart18_checked)) (CutTop2H4NegPart19_checked))))) (CutTop2H4NegPart20_checked)) (CutTop2H4NegPart21_checked))) (CutTop2H4NegPart22_checked)

end HlawkaSchatten.BelowExponent.G3P
