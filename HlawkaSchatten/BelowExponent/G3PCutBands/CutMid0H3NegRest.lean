/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegRestPart6

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H3NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H3NegRestBox : Box := ⟨![27/68, 1/20, 0, -8], ![9/17, 7/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid0H3NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid0H3NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid0H3NegRestPart1Tree) (CutMid0H3NegRestPart2Tree)) (CutMid0H3NegRestPart3Tree)) (CutMid0H3NegRestPart4Tree)) (CutMid0H3NegRestPart5Tree))) (CutMid0H3NegRestPart6Tree)

set_option maxRecDepth 16000 in
theorem CutMid0H3NegRest_ok : CutMid0H3NegRestTree.ok CutMid0H3NegRestBox false (1) = true :=
  RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutMid0H3NegRestPart0_ok) (RatioRemainder.cut_ok (RatioRemainder.cut_ok (RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutMid0H3NegRestPart1_ok) (CutMid0H3NegRestPart2_ok)) (CutMid0H3NegRestPart3_ok)) (CutMid0H3NegRestPart4_ok)) (CutMid0H3NegRestPart5_ok))) (CutMid0H3NegRestPart6_ok)

end HlawkaSchatten.BelowExponent.G3P
