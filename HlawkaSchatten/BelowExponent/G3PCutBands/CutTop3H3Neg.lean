/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegPart25

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H3Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H3NegBox : Box := ⟨![27/136, 9/50, 0, -8], ![9/34, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H3NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop3H3NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H3NegPart1Tree) (.cut 3 (0) (.cut 2 (5/16) (.cut 3 (-1/8) (CutTop3H3NegPart2Tree) (.cut 3 (-1/16) (CutTop3H3NegPart3Tree) (.cut 1 (37/200) (.cut 0 (63/272) (CutTop3H3NegPart4Tree) (CutTop3H3NegPart5Tree)) (.cut 0 (63/272) (CutTop3H3NegPart6Tree) (CutTop3H3NegPart7Tree))))) (.cut 3 (-1/8) (CutTop3H3NegPart8Tree) (.cut 3 (-1/16) (CutTop3H3NegPart9Tree) (.cut 3 (-1/32) (CutTop3H3NegPart10Tree) (.cut 3 (-1/64) (.cut 0 (63/272) (CutTop3H3NegPart11Tree) (CutTop3H3NegPart12Tree)) (.cut 0 (63/272) (CutTop3H3NegPart13Tree) (.cut 3 (-1/128) (CutTop3H3NegPart14Tree) (CutTop3H3NegPart15Tree)))))))) (.cut 2 (5/16) (.cut 3 (1/8) (CutTop3H3NegPart16Tree) (CutTop3H3NegPart17Tree)) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 3 (1/32) (.cut 3 (1/64) (CutTop3H3NegPart18Tree) (CutTop3H3NegPart19Tree)) (CutTop3H3NegPart20Tree)) (CutTop3H3NegPart21Tree)) (CutTop3H3NegPart22Tree))))) (CutTop3H3NegPart23Tree)) (CutTop3H3NegPart24Tree))) (CutTop3H3NegPart25Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H3Neg_checked : CutTop3H3NegTree.commonOK CutTop3H3NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H3NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H3NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H3NegPart2_checked) (CertTree.commonCut_ok (CutTop3H3NegPart3_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H3NegPart4_checked) (CutTop3H3NegPart5_checked)) (CertTree.commonCut_ok (CutTop3H3NegPart6_checked) (CutTop3H3NegPart7_checked))))) (CertTree.commonCut_ok (CutTop3H3NegPart8_checked) (CertTree.commonCut_ok (CutTop3H3NegPart9_checked) (CertTree.commonCut_ok (CutTop3H3NegPart10_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H3NegPart11_checked) (CutTop3H3NegPart12_checked)) (CertTree.commonCut_ok (CutTop3H3NegPart13_checked) (CertTree.commonCut_ok (CutTop3H3NegPart14_checked) (CutTop3H3NegPart15_checked)))))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H3NegPart16_checked) (CutTop3H3NegPart17_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop3H3NegPart18_checked) (CutTop3H3NegPart19_checked)) (CutTop3H3NegPart20_checked)) (CutTop3H3NegPart21_checked)) (CutTop3H3NegPart22_checked))))) (CutTop3H3NegPart23_checked)) (CutTop3H3NegPart24_checked))) (CutTop3H3NegPart25_checked)

end HlawkaSchatten.BelowExponent.G3P
