/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6PosPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6PosPart1

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H6Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H6PosBox : Box := ⟨![27/68, 19/100, 0, -8], ![63/136, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H6PosTree : CertTree :=
  .cut 3 (3/4) (CutTop4H6PosPart0Tree) (CutTop4H6PosPart1Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H6Pos_checked : CutTop4H6PosTree.commonOK CutTop4H6PosBox true = true := CertTree.commonCut_ok (CutTop4H6PosPart0_checked) (CutTop4H6PosPart1_checked)

end HlawkaSchatten.BelowExponent.G3P
