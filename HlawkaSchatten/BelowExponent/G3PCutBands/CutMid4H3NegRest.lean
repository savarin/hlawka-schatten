/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegRestPart5

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3NegRestBox : Box := ⟨![27/68, 13/100, 0, -8], ![9/17, 3/20, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid4H3NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid4H3NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid4H3NegRestPart1Tree) (CutMid4H3NegRestPart2Tree)) (CutMid4H3NegRestPart3Tree)) (CutMid4H3NegRestPart4Tree))) (CutMid4H3NegRestPart5Tree)

set_option maxRecDepth 16000 in
theorem CutMid4H3NegRest_ok : CutMid4H3NegRestTree.geometryOK CutMid4H3NegPowerCache CutMid4H3NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid4H3NegRestPart0_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid4H3NegRestPart1_ok) (CutMid4H3NegRestPart2_ok)) (CutMid4H3NegRestPart3_ok)) (CutMid4H3NegRestPart4_ok))) (CutMid4H3NegRestPart5_ok)

end HlawkaSchatten.BelowExponent.G3P
