/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegRestPart15

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegRestBox : Box := ⟨![27/68, 7/100, 0, -8], ![9/17, 9/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid1H3NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid1H3NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (.cut 1 (2/25) (CutMid1H3NegRestPart1Tree) (.cut 1 (17/200) (CutMid1H3NegRestPart2Tree) (.cut 3 (-1/8) (CutMid1H3NegRestPart3Tree) (.cut 0 (63/136) (CutMid1H3NegRestPart4Tree) (CutMid1H3NegRestPart5Tree))))) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (2/25) (CutMid1H3NegRestPart6Tree) (.cut 3 (1/32) (.cut 1 (17/200) (CutMid1H3NegRestPart7Tree) (CutMid1H3NegRestPart8Tree)) (CutMid1H3NegRestPart9Tree))) (CutMid1H3NegRestPart10Tree)) (CutMid1H3NegRestPart11Tree))) (CutMid1H3NegRestPart12Tree)) (CutMid1H3NegRestPart13Tree)) (CutMid1H3NegRestPart14Tree))) (CutMid1H3NegRestPart15Tree)

set_option maxRecDepth 16000 in
theorem CutMid1H3NegRest_ok : CutMid1H3NegRestTree.ok CutMid1H3NegRestBox false (1) = true :=
  RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutMid1H3NegRestPart0_ok) (RatioRemainder.cut_ok (RatioRemainder.cut_ok (RatioRemainder.cut_ok (RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutMid1H3NegRestPart1_ok) (RatioRemainder.cut_ok (CutMid1H3NegRestPart2_ok) (RatioRemainder.cut_ok (CutMid1H3NegRestPart3_ok) (RatioRemainder.cut_ok (CutMid1H3NegRestPart4_ok) (CutMid1H3NegRestPart5_ok))))) (RatioRemainder.cut_ok (RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutMid1H3NegRestPart6_ok) (RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutMid1H3NegRestPart7_ok) (CutMid1H3NegRestPart8_ok)) (CutMid1H3NegRestPart9_ok))) (CutMid1H3NegRestPart10_ok)) (CutMid1H3NegRestPart11_ok))) (CutMid1H3NegRestPart12_ok)) (CutMid1H3NegRestPart13_ok)) (CutMid1H3NegRestPart14_ok))) (CutMid1H3NegRestPart15_ok)

end HlawkaSchatten.BelowExponent.G3P
