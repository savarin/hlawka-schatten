/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H6NegPart21

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H6Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H6NegBox : Box := ⟨![27/68, 17/100, 0, -8], ![63/136, 9/50, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop2H6NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop2H6NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop2H6NegPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (CutTop2H6NegPart2Tree) (.cut 2 (5/16) (.cut 1 (7/40) (CutTop2H6NegPart3Tree) (CutTop2H6NegPart4Tree)) (.cut 3 (-1/16) (CutTop2H6NegPart5Tree) (.cut 3 (-1/32) (CutTop2H6NegPart6Tree) (.cut 3 (-1/64) (CutTop2H6NegPart7Tree) (.cut 0 (117/272) (CutTop2H6NegPart8Tree) (CutTop2H6NegPart9Tree))))))) (.cut 2 (5/16) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 2 (7/32) (CutTop2H6NegPart10Tree) (CutTop2H6NegPart11Tree)) (CutTop2H6NegPart12Tree)) (CutTop2H6NegPart13Tree)) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 3 (1/32) (.cut 2 (13/32) (CutTop2H6NegPart14Tree) (CutTop2H6NegPart15Tree)) (CutTop2H6NegPart16Tree)) (CutTop2H6NegPart17Tree)) (CutTop2H6NegPart18Tree))))) (CutTop2H6NegPart19Tree)) (CutTop2H6NegPart20Tree))) (CutTop2H6NegPart21Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H6Neg_checked : CutTop2H6NegTree.commonOK CutTop2H6NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H6NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H6NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H6NegPart2_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H6NegPart3_checked) (CutTop2H6NegPart4_checked)) (CertTree.commonCut_ok (CutTop2H6NegPart5_checked) (CertTree.commonCut_ok (CutTop2H6NegPart6_checked) (CertTree.commonCut_ok (CutTop2H6NegPart7_checked) (CertTree.commonCut_ok (CutTop2H6NegPart8_checked) (CutTop2H6NegPart9_checked))))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H6NegPart10_checked) (CutTop2H6NegPart11_checked)) (CutTop2H6NegPart12_checked)) (CutTop2H6NegPart13_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H6NegPart14_checked) (CutTop2H6NegPart15_checked)) (CutTop2H6NegPart16_checked)) (CutTop2H6NegPart17_checked)) (CutTop2H6NegPart18_checked))))) (CutTop2H6NegPart19_checked)) (CutTop2H6NegPart20_checked))) (CutTop2H6NegPart21_checked)

end HlawkaSchatten.BelowExponent.G3P
