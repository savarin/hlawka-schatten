/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegRestPart2

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H2NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H2NegRestBox : Box := ⟨![9/68, 4/25, 0, -8], ![27/136, 17/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop1H2NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop1H2NegRestPart0Tree) (CutTop1H2NegRestPart1Tree)) (CutTop1H2NegRestPart2Tree)

set_option maxRecDepth 16000 in
theorem CutTop1H2NegRest_ok : CutTop1H2NegRestTree.ok CutTop1H2NegRestBox false (1) = true :=
  RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutTop1H2NegRestPart0_ok) (CutTop1H2NegRestPart1_ok)) (CutTop1H2NegRestPart2_ok)

end HlawkaSchatten.BelowExponent.G3P
