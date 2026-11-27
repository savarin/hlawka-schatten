/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegRestPart1

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H2NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H2NegRestBox : Box := ⟨![9/68, 3/20, 0, -8], ![27/136, 4/25, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop0H2NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (CutTop0H2NegRestPart0Tree) (CutTop0H2NegRestPart1Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H2NegRest_ok : CutTop0H2NegRestTree.ok CutTop0H2NegRestBox false (1) = true :=
  RatioRemainder.cut_ok (CutTop0H2NegRestPart0_ok) (CutTop0H2NegRestPart1_ok)

end HlawkaSchatten.BelowExponent.G3P
