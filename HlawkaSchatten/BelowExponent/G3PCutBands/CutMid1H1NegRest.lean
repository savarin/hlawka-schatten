/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegRestPart5

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H1NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H1NegRestBox : Box := ⟨![9/68, 7/100, 0, -8], ![9/34, 9/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid1H1NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid1H1NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid1H1NegRestPart1Tree) (CutMid1H1NegRestPart2Tree)) (CutMid1H1NegRestPart3Tree)) (CutMid1H1NegRestPart4Tree))) (CutMid1H1NegRestPart5Tree)

set_option maxRecDepth 16000 in
theorem CutMid1H1NegRest_ok : CutMid1H1NegRestTree.geometryOK CutMid1H1NegPowerCache CutMid1H1NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid1H1NegRestPart0_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid1H1NegRestPart1_ok) (CutMid1H1NegRestPart2_ok)) (CutMid1H1NegRestPart3_ok)) (CutMid1H1NegRestPart4_ok))) (CutMid1H1NegRestPart5_ok)

end HlawkaSchatten.BelowExponent.G3P
