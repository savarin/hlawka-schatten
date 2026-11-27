/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3PosPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3PosPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3PosPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3PosPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3PosPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3PosPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3PosPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3PosPart7

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3PosBox : Box := ⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid3H3PosTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid3H3PosPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid3H3PosPart1Tree) (.cut 2 (5/16) (.cut 1 (3/25) (CutMid3H3PosPart2Tree) (CutMid3H3PosPart3Tree)) (CutMid3H3PosPart4Tree))) (CutMid3H3PosPart5Tree)) (CutMid3H3PosPart6Tree))) (CutMid3H3PosPart7Tree)

set_option maxRecDepth 16000 in
theorem CutMid3H3Pos_checked : CutMid3H3PosTree.commonOK CutMid3H3PosBox true = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H3PosPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H3PosPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid3H3PosPart2_checked) (CutMid3H3PosPart3_checked)) (CutMid3H3PosPart4_checked))) (CutMid3H3PosPart5_checked)) (CutMid3H3PosPart6_checked))) (CutMid3H3PosPart7_checked)

end HlawkaSchatten.BelowExponent.G3P
