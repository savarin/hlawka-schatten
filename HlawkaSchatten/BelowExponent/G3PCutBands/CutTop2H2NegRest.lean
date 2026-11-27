/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegRestPart3

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H2NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H2NegRestBox : Box := ⟨![9/68, 17/100, 0, -8], ![27/136, 9/50, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop2H2NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop2H2NegRestPart0Tree) (.cut 3 (1/4) (CutTop2H2NegRestPart1Tree) (CutTop2H2NegRestPart2Tree))) (CutTop2H2NegRestPart3Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H2NegRest_ok : CutTop2H2NegRestTree.ok CutTop2H2NegRestBox false (1) = true :=
  RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutTop2H2NegRestPart0_ok) (RatioRemainder.cut_ok (CutTop2H2NegRestPart1_ok) (CutTop2H2NegRestPart2_ok))) (CutTop2H2NegRestPart3_ok)

end HlawkaSchatten.BelowExponent.G3P
