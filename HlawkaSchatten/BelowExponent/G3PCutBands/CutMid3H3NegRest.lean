/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegRestPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegRestPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegRestPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegRestPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegRestPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegRestPart11

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3NegRestBox : Box := ⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid3H3NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid3H3NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid3H3NegRestPart1Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (3/25) (.cut 3 (1/32) (.cut 1 (23/200) (CutMid3H3NegRestPart2Tree) (CutMid3H3NegRestPart3Tree)) (CutMid3H3NegRestPart4Tree)) (CutMid3H3NegRestPart5Tree)) (CutMid3H3NegRestPart6Tree)) (CutMid3H3NegRestPart7Tree))) (CutMid3H3NegRestPart8Tree)) (CutMid3H3NegRestPart9Tree)) (CutMid3H3NegRestPart10Tree))) (CutMid3H3NegRestPart11Tree)

set_option maxRecDepth 16000 in
theorem CutMid3H3NegRest_ok : CutMid3H3NegRestTree.geometryOK CutMid3H3NegPowerCache CutMid3H3NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid3H3NegRestPart0_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid3H3NegRestPart1_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid3H3NegRestPart2_ok) (CutMid3H3NegRestPart3_ok)) (CutMid3H3NegRestPart4_ok)) (CutMid3H3NegRestPart5_ok)) (CutMid3H3NegRestPart6_ok)) (CutMid3H3NegRestPart7_ok))) (CutMid3H3NegRestPart8_ok)) (CutMid3H3NegRestPart9_ok)) (CutMid3H3NegRestPart10_ok))) (CutMid3H3NegRestPart11_ok)

end HlawkaSchatten.BelowExponent.G3P
