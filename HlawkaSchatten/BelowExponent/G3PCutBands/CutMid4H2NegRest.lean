/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegRestPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegRestPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegRestPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegRestPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegRestPart10

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H2NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H2NegRestBox : Box := ⟨![9/34, 13/100, 0, -8], ![27/68, 3/20, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid4H2NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid4H2NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid4H2NegRestPart1Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (7/50) (.cut 1 (27/200) (CutMid4H2NegRestPart2Tree) (CutMid4H2NegRestPart3Tree)) (CutMid4H2NegRestPart4Tree)) (CutMid4H2NegRestPart5Tree)) (CutMid4H2NegRestPart6Tree))) (CutMid4H2NegRestPart7Tree)) (CutMid4H2NegRestPart8Tree)) (CutMid4H2NegRestPart9Tree))) (CutMid4H2NegRestPart10Tree)

set_option maxRecDepth 16000 in
theorem CutMid4H2NegRest_ok : CutMid4H2NegRestTree.geometryOK CutMid4H2NegPowerCache CutMid4H2NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid4H2NegRestPart0_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid4H2NegRestPart1_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid4H2NegRestPart2_ok) (CutMid4H2NegRestPart3_ok)) (CutMid4H2NegRestPart4_ok)) (CutMid4H2NegRestPart5_ok)) (CutMid4H2NegRestPart6_ok))) (CutMid4H2NegRestPart7_ok)) (CutMid4H2NegRestPart8_ok)) (CutMid4H2NegRestPart9_ok))) (CutMid4H2NegRestPart10_ok)

end HlawkaSchatten.BelowExponent.G3P
