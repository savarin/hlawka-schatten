/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegRestPart1

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H4NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H4NegRestBox : Box := ⟨![9/34, 17/100, 0, -8], ![45/136, 9/50, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop2H4NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (CutTop2H4NegRestPart0Tree) (CutTop2H4NegRestPart1Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H4NegRest_ok : CutTop2H4NegRestTree.geometryOK CutTop2H4NegPowerCache CutTop2H4NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (CutTop2H4NegRestPart0_ok) (CutTop2H4NegRestPart1_ok)

end HlawkaSchatten.BelowExponent.G3P
