/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3PosPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3PosPart1

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H3Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H3PosBox : Box := ⟨![27/68, 1/20, 0, -8], ![9/17, 7/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid0H3PosTree : CertTree :=
  .cut 3 (3/4) (CutMid0H3PosPart0Tree) (CutMid0H3PosPart1Tree)

set_option maxRecDepth 16000 in
theorem CutMid0H3Pos_checked : CutMid0H3PosTree.commonOK CutMid0H3PosBox true = true := CertTree.commonCut_ok (CutMid0H3PosPart0_checked) (CutMid0H3PosPart1_checked)

end HlawkaSchatten.BelowExponent.G3P
