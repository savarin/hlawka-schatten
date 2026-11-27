/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7NegRestPart1

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H7NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H7NegRestBox : Box := ⟨![63/136, 4/25, 0, -8], ![9/17, 17/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop1H7NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (CutTop1H7NegRestPart0Tree) (CutTop1H7NegRestPart1Tree)

set_option maxRecDepth 16000 in
theorem CutTop1H7NegRest_ok : CutTop1H7NegRestTree.ok CutTop1H7NegRestBox false (1) = true :=
  RatioRemainder.cut_ok (CutTop1H7NegRestPart0_ok) (CutTop1H7NegRestPart1_ok)

end HlawkaSchatten.BelowExponent.G3P
