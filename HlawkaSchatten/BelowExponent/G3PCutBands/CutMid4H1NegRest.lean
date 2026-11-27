/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegRestPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegRestPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegRestPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegRestPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegRestPart10

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H1NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H1NegRestBox : Box := ⟨![9/68, 13/100, 0, -8], ![9/34, 3/20, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid4H1NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid4H1NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid4H1NegRestPart1Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (7/50) (CutMid4H1NegRestPart2Tree) (CutMid4H1NegRestPart3Tree)) (CutMid4H1NegRestPart4Tree)) (CutMid4H1NegRestPart5Tree))) (CutMid4H1NegRestPart6Tree)) (CutMid4H1NegRestPart7Tree)) (.cut 2 (1/2) (CutMid4H1NegRestPart8Tree) (CutMid4H1NegRestPart9Tree)))) (CutMid4H1NegRestPart10Tree)

set_option maxRecDepth 16000 in
theorem CutMid4H1NegRest_ok : CutMid4H1NegRestTree.geometryOK CutMid4H1NegPowerCache CutMid4H1NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid4H1NegRestPart0_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid4H1NegRestPart1_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid4H1NegRestPart2_ok) (CutMid4H1NegRestPart3_ok)) (CutMid4H1NegRestPart4_ok)) (CutMid4H1NegRestPart5_ok))) (CutMid4H1NegRestPart6_ok)) (CutMid4H1NegRestPart7_ok)) (RatioRemainder.geometryCut_ok (CutMid4H1NegRestPart8_ok) (CutMid4H1NegRestPart9_ok)))) (CutMid4H1NegRestPart10_ok)

end HlawkaSchatten.BelowExponent.G3P
