/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3PosPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3PosPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3PosPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3PosPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3PosPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3PosPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3PosPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3PosPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3PosPart8

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3PosBox : Box := ⟨![27/68, 13/100, 0, -8], ![9/17, 3/20, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid4H3PosTree : CertTree :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid4H3PosPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid4H3PosPart1Tree) (.cut 2 (5/16) (.cut 1 (7/50) (CutMid4H3PosPart2Tree) (CutMid4H3PosPart3Tree)) (.cut 2 (13/32) (CutMid4H3PosPart4Tree) (CutMid4H3PosPart5Tree)))) (CutMid4H3PosPart6Tree)) (CutMid4H3PosPart7Tree))) (CutMid4H3PosPart8Tree)

set_option maxRecDepth 16000 in
theorem CutMid4H3Pos_checked : CutMid4H3PosTree.commonOK CutMid4H3PosBox true = true := CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H3PosPart0_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H3PosPart1_checked) (CertTree.commonCut_ok (CertTree.commonCut_ok (CutMid4H3PosPart2_checked) (CutMid4H3PosPart3_checked)) (CertTree.commonCut_ok (CutMid4H3PosPart4_checked) (CutMid4H3PosPart5_checked)))) (CutMid4H3PosPart6_checked)) (CutMid4H3PosPart7_checked))) (CutMid4H3PosPart8_checked)

end HlawkaSchatten.BelowExponent.G3P
