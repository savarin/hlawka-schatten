/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2PosPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2PosPart1

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H2Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H2PosBox : Box := ⟨![9/34, 13/100, 0, -8], ![27/68, 3/20, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid4H2PosTree : CertTree :=
  .cut 3 (3/4) (CutMid4H2PosPart0Tree) (CutMid4H2PosPart1Tree)

set_option maxRecDepth 16000 in
theorem CutMid4H2Pos_checked : CutMid4H2PosTree.commonOK CutMid4H2PosBox true = true := CertTree.commonCut_ok (CutMid4H2PosPart0_checked) (CutMid4H2PosPart1_checked)

end HlawkaSchatten.BelowExponent.G3P
