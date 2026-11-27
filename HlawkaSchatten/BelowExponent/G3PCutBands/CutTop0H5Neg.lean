/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegPart10

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H5Neg`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H5NegBox : Box := ⟨![45/136, 3/20, 0, -8], ![27/68, 4/25, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop0H5NegTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop0H5NegPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop0H5NegPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop0H5NegPart2Tree) (.cut 1 (31/200) (CutTop0H5NegPart3Tree) (CutTop0H5NegPart4Tree))) (CutTop0H5NegPart5Tree)) (.cut 3 (0) (CutTop0H5NegPart6Tree) (CutTop0H5NegPart7Tree)))) (CutTop0H5NegPart8Tree)) (CutTop0H5NegPart9Tree))) (CutTop0H5NegPart10Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H5Neg_checked : CutTop0H5NegTree.commonOK CutTop0H5NegBox false = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H5NegPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H5NegPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutTop0H5NegPart2_checked) (CertTree.commonCut_ok (CutTop0H5NegPart3_checked) (CutTop0H5NegPart4_checked))) (CutTop0H5NegPart5_checked)) (CertTree.commonCut_ok (CutTop0H5NegPart6_checked) (CutTop0H5NegPart7_checked)))) (CutTop0H5NegPart8_checked)) (CutTop0H5NegPart9_checked))) (CutTop0H5NegPart10_checked)

end HlawkaSchatten.BelowExponent.G3P
