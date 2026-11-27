/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegRestPart6

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H3NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H3NegRestBox : Box := ⟨![27/136, 19/100, 0, -8], ![9/34, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H3NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop4H3NegRestPart0Tree) (.cut 3 (1/4) (CutTop4H3NegRestPart1Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H3NegRestPart2Tree) (.cut 0 (63/272) (CutTop4H3NegRestPart3Tree) (CutTop4H3NegRestPart4Tree))) (CutTop4H3NegRestPart5Tree)))) (CutTop4H3NegRestPart6Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H3NegRest_ok : CutTop4H3NegRestTree.ok CutTop4H3NegRestBox false (1) = true :=
  RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutTop4H3NegRestPart0_ok) (RatioRemainder.cut_ok (CutTop4H3NegRestPart1_ok) (RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutTop4H3NegRestPart2_ok) (RatioRemainder.cut_ok (CutTop4H3NegRestPart3_ok) (CutTop4H3NegRestPart4_ok))) (CutTop4H3NegRestPart5_ok)))) (CutTop4H3NegRestPart6_ok)

end HlawkaSchatten.BelowExponent.G3P
