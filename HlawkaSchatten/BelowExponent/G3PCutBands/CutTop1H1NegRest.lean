/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H1NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H1NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H1NegRestPart2

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H1NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H1NegRestBox : Box := ⟨![9/136, 4/25, 0, -8], ![9/68, 17/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop1H1NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop1H1NegRestPart0Tree) (CutTop1H1NegRestPart1Tree)) (CutTop1H1NegRestPart2Tree)

set_option maxRecDepth 16000 in
theorem CutTop1H1NegRest_ok : CutTop1H1NegRestTree.ok CutTop1H1NegRestBox false (1) = true :=
  RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutTop1H1NegRestPart0_ok) (CutTop1H1NegRestPart1_ok)) (CutTop1H1NegRestPart2_ok)

end HlawkaSchatten.BelowExponent.G3P
