/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegPart22

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H5Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H5NegBox : Box := ⟨![45/136, 17/100, 0, -8], ![27/68, 9/50, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop2H5NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop2H5NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop2H5NegPart1Tree) (.cut 3 (0) (.cut 2 (5/16) (.cut 3 (-1/8) (CutTop2H5NegPart2Tree) (.cut 3 (-1/16) (CutTop2H5NegPart3Tree) (.cut 1 (7/40) (CutTop2H5NegPart4Tree) (CutTop2H5NegPart5Tree)))) (.cut 3 (-1/8) (CutTop2H5NegPart6Tree) (.cut 3 (-1/16) (CutTop2H5NegPart7Tree) (.cut 3 (-1/32) (CutTop2H5NegPart8Tree) (.cut 3 (-1/64) (CutTop2H5NegPart9Tree) (.cut 0 (99/272) (CutTop2H5NegPart10Tree) (CutTop2H5NegPart11Tree))))))) (.cut 2 (5/16) (.cut 3 (1/8) (.cut 3 (1/16) (CutTop2H5NegPart12Tree) (CutTop2H5NegPart13Tree)) (CutTop2H5NegPart14Tree)) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 3 (1/32) (.cut 3 (1/64) (CutTop2H5NegPart15Tree) (CutTop2H5NegPart16Tree)) (CutTop2H5NegPart17Tree)) (CutTop2H5NegPart18Tree)) (CutTop2H5NegPart19Tree))))) (CutTop2H5NegPart20Tree)) (CutTop2H5NegPart21Tree))) (CutTop2H5NegPart22Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H5Neg_checked : CutTop2H5NegTree.commonOK CutTop2H5NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H5NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H5NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H5NegPart2_checked) (CertTree.commonCut_ok (CutTop2H5NegPart3_checked) (CertTree.commonCut_ok (CutTop2H5NegPart4_checked) (CutTop2H5NegPart5_checked)))) (CertTree.commonCut_ok (CutTop2H5NegPart6_checked) (CertTree.commonCut_ok (CutTop2H5NegPart7_checked) (CertTree.commonCut_ok (CutTop2H5NegPart8_checked) (CertTree.commonCut_ok (CutTop2H5NegPart9_checked) (CertTree.commonCut_ok (CutTop2H5NegPart10_checked) (CutTop2H5NegPart11_checked))))))) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H5NegPart12_checked) (CutTop2H5NegPart13_checked)) (CutTop2H5NegPart14_checked)) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop2H5NegPart15_checked) (CutTop2H5NegPart16_checked)) (CutTop2H5NegPart17_checked)) (CutTop2H5NegPart18_checked)) (CutTop2H5NegPart19_checked))))) (CutTop2H5NegPart20_checked)) (CutTop2H5NegPart21_checked))) (CutTop2H5NegPart22_checked)

end HlawkaSchatten.BelowExponent.G3P
