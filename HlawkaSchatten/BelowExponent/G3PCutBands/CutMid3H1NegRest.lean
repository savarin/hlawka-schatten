/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegRestPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegRestPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegRestPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegRestPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegRestPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegRestPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegRestPart12

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H1NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H1NegRestBox : Box := ⟨![9/68, 11/100, 0, -8], ![9/34, 13/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid3H1NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid3H1NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid3H1NegRestPart1Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (3/25) (.cut 1 (23/200) (.cut 0 (27/136) (CutMid3H1NegRestPart2Tree) (CutMid3H1NegRestPart3Tree)) (CutMid3H1NegRestPart4Tree)) (.cut 1 (1/8) (CutMid3H1NegRestPart5Tree) (CutMid3H1NegRestPart6Tree))) (CutMid3H1NegRestPart7Tree)) (CutMid3H1NegRestPart8Tree))) (CutMid3H1NegRestPart9Tree)) (CutMid3H1NegRestPart10Tree)) (CutMid3H1NegRestPart11Tree))) (CutMid3H1NegRestPart12Tree)

set_option maxRecDepth 16000 in
theorem CutMid3H1NegRest_ok : CutMid3H1NegRestTree.geometryOK CutMid3H1NegPowerCache CutMid3H1NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid3H1NegRestPart0_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid3H1NegRestPart1_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid3H1NegRestPart2_ok) (CutMid3H1NegRestPart3_ok)) (CutMid3H1NegRestPart4_ok)) (RatioRemainder.geometryCut_ok (CutMid3H1NegRestPart5_ok) (CutMid3H1NegRestPart6_ok))) (CutMid3H1NegRestPart7_ok)) (CutMid3H1NegRestPart8_ok))) (CutMid3H1NegRestPart9_ok)) (CutMid3H1NegRestPart10_ok)) (CutMid3H1NegRestPart11_ok))) (CutMid3H1NegRestPart12_ok)

end HlawkaSchatten.BelowExponent.G3P
