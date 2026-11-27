/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegRestPart2

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H5NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H5NegRestBox : Box := ⟨![45/136, 9/50, 0, -8], ![27/68, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H5NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop3H5NegRestPart0Tree) (CutTop3H5NegRestPart1Tree)) (CutTop3H5NegRestPart2Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H5NegRest_ok : CutTop3H5NegRestTree.geometryOK CutTop3H5NegPowerCache CutTop3H5NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutTop3H5NegRestPart0_ok) (CutTop3H5NegRestPart1_ok)) (CutTop3H5NegRestPart2_ok)

end HlawkaSchatten.BelowExponent.G3P
