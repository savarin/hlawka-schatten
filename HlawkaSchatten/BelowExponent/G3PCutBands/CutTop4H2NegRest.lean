/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegRestPart5

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegRestBox : Box := ⟨![9/68, 19/100, 0, -8], ![27/136, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H2NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop4H2NegRestPart0Tree) (.cut 3 (1/4) (CutTop4H2NegRestPart1Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H2NegRestPart2Tree) (CutTop4H2NegRestPart3Tree)) (CutTop4H2NegRestPart4Tree)))) (CutTop4H2NegRestPart5Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H2NegRest_ok : CutTop4H2NegRestTree.geometryOK CutTop4H2NegPowerCache CutTop4H2NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutTop4H2NegRestPart0_ok) (RatioRemainder.geometryCut_ok (CutTop4H2NegRestPart1_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutTop4H2NegRestPart2_ok) (CutTop4H2NegRestPart3_ok)) (CutTop4H2NegRestPart4_ok)))) (CutTop4H2NegRestPart5_ok)

end HlawkaSchatten.BelowExponent.G3P
