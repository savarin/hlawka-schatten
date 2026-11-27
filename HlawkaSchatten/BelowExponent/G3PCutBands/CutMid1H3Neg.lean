/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegPart21

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegBox : Box := ⟨![27/68, 7/100, 0, -8], ![9/17, 9/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid1H3NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid1H3NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (.cut 1 (2/25) (.cut 1 (3/40) (CutMid1H3NegPart1Tree) (CutMid1H3NegPart2Tree)) (.cut 1 (17/200) (CutMid1H3NegPart3Tree) (.cut 3 (-1/8) (CutMid1H3NegPart4Tree) (.cut 0 (63/136) (CutMid1H3NegPart5Tree) (CutMid1H3NegPart6Tree))))) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (2/25) (CutMid1H3NegPart7Tree) (.cut 3 (1/32) (.cut 1 (17/200) (CutMid1H3NegPart8Tree) (.cut 0 (63/136) (CutMid1H3NegPart9Tree) (CutMid1H3NegPart10Tree))) (CutMid1H3NegPart11Tree))) (CutMid1H3NegPart12Tree)) (CutMid1H3NegPart13Tree))) (.cut 2 (5/16) (.cut 3 (0) (.cut 2 (7/32) (.cut 1 (2/25) (CutMid1H3NegPart14Tree) (CutMid1H3NegPart15Tree)) (CutMid1H3NegPart16Tree)) (CutMid1H3NegPart17Tree)) (CutMid1H3NegPart18Tree))) (CutMid1H3NegPart19Tree)) (CutMid1H3NegPart20Tree))) (CutMid1H3NegPart21Tree)

set_option maxRecDepth 16000 in
theorem CutMid1H3Neg_checked : CutMid1H3NegTree.commonOK CutMid1H3NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid1H3NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid1H3NegPart1_checked) (CutMid1H3NegPart2_checked)) (CertTree.commonCut_ok (CutMid1H3NegPart3_checked) (CertTree.commonCut_ok (CutMid1H3NegPart4_checked) (CertTree.commonCut_ok (CutMid1H3NegPart5_checked) (CutMid1H3NegPart6_checked))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid1H3NegPart7_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid1H3NegPart8_checked) (CertTree.commonCut_ok (CutMid1H3NegPart9_checked) (CutMid1H3NegPart10_checked))) (CutMid1H3NegPart11_checked))) (CutMid1H3NegPart12_checked)) (CutMid1H3NegPart13_checked))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid1H3NegPart14_checked) (CutMid1H3NegPart15_checked)) (CutMid1H3NegPart16_checked)) (CutMid1H3NegPart17_checked)) (CutMid1H3NegPart18_checked))) (CutMid1H3NegPart19_checked)) (CutMid1H3NegPart20_checked))) (CutMid1H3NegPart21_checked)

end HlawkaSchatten.BelowExponent.G3P
