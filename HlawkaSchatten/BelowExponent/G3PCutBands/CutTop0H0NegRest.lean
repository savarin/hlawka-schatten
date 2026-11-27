/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegRestPart2

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H0NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H0NegRestBox : Box := ⟨![0, 3/20, 0, -8], ![9/136, 4/25, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop0H0NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop0H0NegRestPart0Tree) (CutTop0H0NegRestPart1Tree)) (CutTop0H0NegRestPart2Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H0NegRest_ok : CutTop0H0NegRestTree.geometryOK CutTop0H0NegPowerCache CutTop0H0NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutTop0H0NegRestPart0_ok) (CutTop0H0NegRestPart1_ok)) (CutTop0H0NegRestPart2_ok)

end HlawkaSchatten.BelowExponent.G3P
