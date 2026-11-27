/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegRestPart3

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H7NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H7NegRestBox : Box := ⟨![63/136, 17/100, 0, -8], ![9/17, 9/50, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop2H7NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop2H7NegRestPart0Tree) (.cut 3 (1/4) (CutTop2H7NegRestPart1Tree) (CutTop2H7NegRestPart2Tree))) (CutTop2H7NegRestPart3Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H7NegRest_ok : CutTop2H7NegRestTree.geometryOK CutTop2H7NegPowerCache CutTop2H7NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutTop2H7NegRestPart0_ok) (RatioRemainder.geometryCut_ok (CutTop2H7NegRestPart1_ok) (CutTop2H7NegRestPart2_ok))) (CutTop2H7NegRestPart3_ok)

end HlawkaSchatten.BelowExponent.G3P
