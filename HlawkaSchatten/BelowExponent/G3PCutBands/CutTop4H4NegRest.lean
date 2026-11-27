/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegRestPart6

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H4NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H4NegRestBox : Box := ⟨![9/34, 19/100, 0, -8], ![45/136, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H4NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop4H4NegRestPart0Tree) (.cut 3 (1/4) (CutTop4H4NegRestPart1Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H4NegRestPart2Tree) (.cut 0 (81/272) (CutTop4H4NegRestPart3Tree) (CutTop4H4NegRestPart4Tree))) (CutTop4H4NegRestPart5Tree)))) (CutTop4H4NegRestPart6Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H4NegRest_ok : CutTop4H4NegRestTree.geometryOK CutTop4H4NegPowerCache CutTop4H4NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutTop4H4NegRestPart0_ok) (RatioRemainder.geometryCut_ok (CutTop4H4NegRestPart1_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutTop4H4NegRestPart2_ok) (RatioRemainder.geometryCut_ok (CutTop4H4NegRestPart3_ok) (CutTop4H4NegRestPart4_ok))) (CutTop4H4NegRestPart5_ok)))) (CutTop4H4NegRestPart6_ok)

end HlawkaSchatten.BelowExponent.G3P
