/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6PosPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6PosPart1

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H6Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H6PosBox : Box := ⟨![27/68, 9/50, 0, -8], ![63/136, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H6PosTree : CertTree :=
  .cut 3 (3/4) (CutTop3H6PosPart0Tree) (CutTop3H6PosPart1Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H6Pos_checked : CutTop3H6PosTree.commonOK CutTop3H6PosBox true = true := CertTree.commonCut_ok (CutTop3H6PosPart0_checked) (CutTop3H6PosPart1_checked)

end HlawkaSchatten.BelowExponent.G3P
