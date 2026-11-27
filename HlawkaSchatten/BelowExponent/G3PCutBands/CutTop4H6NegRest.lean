/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegRestPart6

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H6NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H6NegRestBox : Box := ⟨![27/68, 19/100, 0, -8], ![63/136, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H6NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop4H6NegRestPart0Tree) (.cut 3 (1/4) (CutTop4H6NegRestPart1Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H6NegRestPart2Tree) (.cut 0 (117/272) (CutTop4H6NegRestPart3Tree) (CutTop4H6NegRestPart4Tree))) (CutTop4H6NegRestPart5Tree)))) (CutTop4H6NegRestPart6Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H6NegRest_ok : CutTop4H6NegRestTree.ok CutTop4H6NegRestBox false (1) = true :=
  RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutTop4H6NegRestPart0_ok) (RatioRemainder.cut_ok (CutTop4H6NegRestPart1_ok) (RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutTop4H6NegRestPart2_ok) (RatioRemainder.cut_ok (CutTop4H6NegRestPart3_ok) (CutTop4H6NegRestPart4_ok))) (CutTop4H6NegRestPart5_ok)))) (CutTop4H6NegRestPart6_ok)

end HlawkaSchatten.BelowExponent.G3P
