/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegRestPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegRestPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegRestPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegRestPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegRestPart10

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H0NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H0NegRestBox : Box := ⟨![0, 13/100, 0, -8], ![9/68, 3/20, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid4H0NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid4H0NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid4H0NegRestPart1Tree) (.cut 3 (1/8) (.cut 1 (7/50) (CutMid4H0NegRestPart2Tree) (CutMid4H0NegRestPart3Tree)) (CutMid4H0NegRestPart4Tree))) (CutMid4H0NegRestPart5Tree)) (CutMid4H0NegRestPart6Tree)) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid4H0NegRestPart7Tree) (CutMid4H0NegRestPart8Tree)) (CutMid4H0NegRestPart9Tree)))) (CutMid4H0NegRestPart10Tree)

set_option maxRecDepth 16000 in
theorem CutMid4H0NegRest_ok : CutMid4H0NegRestTree.ok CutMid4H0NegRestBox false (1) = true :=
  RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutMid4H0NegRestPart0_ok) (RatioRemainder.cut_ok (RatioRemainder.cut_ok (RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutMid4H0NegRestPart1_ok) (RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutMid4H0NegRestPart2_ok) (CutMid4H0NegRestPart3_ok)) (CutMid4H0NegRestPart4_ok))) (CutMid4H0NegRestPart5_ok)) (CutMid4H0NegRestPart6_ok)) (RatioRemainder.cut_ok (RatioRemainder.cut_ok (CutMid4H0NegRestPart7_ok) (CutMid4H0NegRestPart8_ok)) (CutMid4H0NegRestPart9_ok)))) (CutMid4H0NegRestPart10_ok)

end HlawkaSchatten.BelowExponent.G3P
