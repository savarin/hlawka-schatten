/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegRestPart3

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H0NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H0NegRestBox : Box := ⟨![0, 9/50, 0, -8], ![9/136, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H0NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop3H0NegRestPart0Tree) (.cut 3 (1/4) (CutTop3H0NegRestPart1Tree) (CutTop3H0NegRestPart2Tree))) (CutTop3H0NegRestPart3Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H0NegRest_ok : CutTop3H0NegRestTree.geometryOK CutTop3H0NegPowerCache CutTop3H0NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutTop3H0NegRestPart0_ok) (RatioRemainder.geometryCut_ok (CutTop3H0NegRestPart1_ok) (CutTop3H0NegRestPart2_ok))) (CutTop3H0NegRestPart3_ok)

end HlawkaSchatten.BelowExponent.G3P
