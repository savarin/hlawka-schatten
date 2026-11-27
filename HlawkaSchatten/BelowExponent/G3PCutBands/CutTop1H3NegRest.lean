/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H3NegRestPart1

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H3NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H3NegRestBox : Box := ⟨![27/136, 4/25, 0, -8], ![9/34, 17/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop1H3NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (CutTop1H3NegRestPart0Tree) (CutTop1H3NegRestPart1Tree)

set_option maxRecDepth 16000 in
theorem CutTop1H3NegRest_ok : CutTop1H3NegRestTree.geometryOK CutTop1H3NegPowerCache CutTop1H3NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (CutTop1H3NegRestPart0_ok) (CutTop1H3NegRestPart1_ok)

end HlawkaSchatten.BelowExponent.G3P
