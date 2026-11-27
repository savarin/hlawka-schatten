/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H5NegPart14

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H5Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H5NegBox : Box := ⟨![45/136, 4/25, 0, -8], ![27/68, 17/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop1H5NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop1H5NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop1H5NegPart1Tree) (.cut 3 (0) (.cut 2 (5/16) (.cut 3 (-1/8) (CutTop1H5NegPart2Tree) (.cut 1 (33/200) (CutTop1H5NegPart3Tree) (CutTop1H5NegPart4Tree))) (.cut 3 (-1/8) (CutTop1H5NegPart5Tree) (.cut 3 (-1/16) (CutTop1H5NegPart6Tree) (.cut 3 (-1/32) (CutTop1H5NegPart7Tree) (.cut 3 (-1/64) (CutTop1H5NegPart8Tree) (CutTop1H5NegPart9Tree)))))) (.cut 2 (5/16) (CutTop1H5NegPart10Tree) (CutTop1H5NegPart11Tree)))) (CutTop1H5NegPart12Tree)) (CutTop1H5NegPart13Tree))) (CutTop1H5NegPart14Tree)

set_option maxRecDepth 16000 in
theorem CutTop1H5Neg_checked : CutTop1H5NegTree.commonOK CutTop1H5NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H5NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H5NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop1H5NegPart2_checked) (CertTree.commonCut_ok (CutTop1H5NegPart3_checked) (CutTop1H5NegPart4_checked))) (CertTree.commonCut_ok (CutTop1H5NegPart5_checked) (CertTree.commonCut_ok (CutTop1H5NegPart6_checked) (CertTree.commonCut_ok (CutTop1H5NegPart7_checked) (CertTree.commonCut_ok (CutTop1H5NegPart8_checked) (CutTop1H5NegPart9_checked)))))) (CertTree.commonCut_ok (CutTop1H5NegPart10_checked) (CutTop1H5NegPart11_checked)))) (CutTop1H5NegPart12_checked)) (CutTop1H5NegPart13_checked))) (CutTop1H5NegPart14_checked)

end HlawkaSchatten.BelowExponent.G3P
