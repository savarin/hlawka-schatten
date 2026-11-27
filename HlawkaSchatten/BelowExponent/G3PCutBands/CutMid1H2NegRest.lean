/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegRestPart6

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H2NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H2NegRestBox : Box := ⟨![9/34, 7/100, 0, -8], ![27/68, 9/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid1H2NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid1H2NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid1H2NegRestPart1Tree) (CutMid1H2NegRestPart2Tree)) (CutMid1H2NegRestPart3Tree)) (CutMid1H2NegRestPart4Tree)) (CutMid1H2NegRestPart5Tree))) (CutMid1H2NegRestPart6Tree)

set_option maxRecDepth 16000 in
theorem CutMid1H2NegRest_ok : CutMid1H2NegRestTree.geometryOK CutMid1H2NegPowerCache CutMid1H2NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid1H2NegRestPart0_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid1H2NegRestPart1_ok) (CutMid1H2NegRestPart2_ok)) (CutMid1H2NegRestPart3_ok)) (CutMid1H2NegRestPart4_ok)) (CutMid1H2NegRestPart5_ok))) (CutMid1H2NegRestPart6_ok)

end HlawkaSchatten.BelowExponent.G3P
