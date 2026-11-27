/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegRestPart15

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H2NegRestBox : Box := ⟨![9/34, 11/100, 0, -8], ![27/68, 13/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid3H2NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid3H2NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid3H2NegRestPart1Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (3/25) (.cut 1 (23/200) (.cut 0 (45/136) (CutMid3H2NegRestPart2Tree) (.cut 3 (1/32) (CutMid3H2NegRestPart3Tree) (CutMid3H2NegRestPart4Tree))) (.cut 0 (45/136) (CutMid3H2NegRestPart5Tree) (.cut 3 (1/32) (CutMid3H2NegRestPart6Tree) (CutMid3H2NegRestPart7Tree)))) (.cut 1 (1/8) (CutMid3H2NegRestPart8Tree) (CutMid3H2NegRestPart9Tree))) (CutMid3H2NegRestPart10Tree)) (CutMid3H2NegRestPart11Tree))) (CutMid3H2NegRestPart12Tree)) (CutMid3H2NegRestPart13Tree)) (CutMid3H2NegRestPart14Tree))) (CutMid3H2NegRestPart15Tree)

set_option maxRecDepth 16000 in
theorem CutMid3H2NegRest_ok : CutMid3H2NegRestTree.ok CutMid3H2NegRestBox false (1) = true :=
  RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutMid3H2NegRestPart0_ok) (RatioRemainder.cut_ok (RatioRemainder.cut_ok (RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutMid3H2NegRestPart1_ok) (RatioRemainder.cut_ok (RatioRemainder.cut_ok (RatioRemainder.cut_ok (RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutMid3H2NegRestPart2_ok) (RatioRemainder.cut_ok (CutMid3H2NegRestPart3_ok) (CutMid3H2NegRestPart4_ok))) (RatioRemainder.cut_ok (CutMid3H2NegRestPart5_ok) (RatioRemainder.cut_ok (CutMid3H2NegRestPart6_ok) (CutMid3H2NegRestPart7_ok)))) (RatioRemainder.cut_ok (CutMid3H2NegRestPart8_ok) (CutMid3H2NegRestPart9_ok))) (CutMid3H2NegRestPart10_ok)) (CutMid3H2NegRestPart11_ok))) (CutMid3H2NegRestPart12_ok)) (CutMid3H2NegRestPart13_ok)) (CutMid3H2NegRestPart14_ok))) (CutMid3H2NegRestPart15_ok)

end HlawkaSchatten.BelowExponent.G3P
