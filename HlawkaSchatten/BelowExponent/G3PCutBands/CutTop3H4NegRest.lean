/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegRestPart2

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H4NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H4NegRestBox : Box := ⟨![9/34, 9/50, 0, -8], ![45/136, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H4NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop3H4NegRestPart0Tree) (CutTop3H4NegRestPart1Tree)) (CutTop3H4NegRestPart2Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H4NegRest_ok : CutTop3H4NegRestTree.ok CutTop3H4NegRestBox false (1) = true :=
  RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutTop3H4NegRestPart0_ok) (CutTop3H4NegRestPart1_ok)) (CutTop3H4NegRestPart2_ok)

end HlawkaSchatten.BelowExponent.G3P
