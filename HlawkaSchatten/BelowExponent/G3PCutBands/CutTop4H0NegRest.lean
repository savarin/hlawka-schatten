/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegRestPart5

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H0NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H0NegRestBox : Box := ⟨![0, 19/100, 0, -8], ![9/136, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H0NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop4H0NegRestPart0Tree) (.cut 3 (1/4) (CutTop4H0NegRestPart1Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H0NegRestPart2Tree) (CutTop4H0NegRestPart3Tree)) (CutTop4H0NegRestPart4Tree)))) (CutTop4H0NegRestPart5Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H0NegRest_ok : CutTop4H0NegRestTree.geometryOK CutTop4H0NegPowerCache CutTop4H0NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutTop4H0NegRestPart0_ok) (RatioRemainder.geometryCut_ok (CutTop4H0NegRestPart1_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutTop4H0NegRestPart2_ok) (CutTop4H0NegRestPart3_ok)) (CutTop4H0NegRestPart4_ok)))) (CutTop4H0NegRestPart5_ok)

end HlawkaSchatten.BelowExponent.G3P
