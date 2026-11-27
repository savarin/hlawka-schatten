/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegRestPart2

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H6NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H6NegRestBox : Box := ⟨![27/68, 9/50, 0, -8], ![63/136, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H6NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop3H6NegRestPart0Tree) (CutTop3H6NegRestPart1Tree)) (CutTop3H6NegRestPart2Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H6NegRest_ok : CutTop3H6NegRestTree.geometryOK CutTop3H6NegPowerCache CutTop3H6NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutTop3H6NegRestPart0_ok) (CutTop3H6NegRestPart1_ok)) (CutTop3H6NegRestPart2_ok)

end HlawkaSchatten.BelowExponent.G3P
