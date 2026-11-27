/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegRestPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegRestPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegRestPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegRestPart9

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7NegRestBox : Box := ⟨![63/136, 19/100, 0, -8], ![9/17, 1/5, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop4H7NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutTop4H7NegRestPart0Tree) (.cut 3 (1/4) (CutTop4H7NegRestPart1Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H7NegRestPart2Tree) (.cut 0 (135/272) (CutTop4H7NegRestPart3Tree) (.cut 3 (1/2) (.cut 3 (3/8) (.cut 0 (279/544) (CutTop4H7NegRestPart4Tree) (CutTop4H7NegRestPart5Tree)) (CutTop4H7NegRestPart6Tree)) (CutTop4H7NegRestPart7Tree)))) (CutTop4H7NegRestPart8Tree)))) (CutTop4H7NegRestPart9Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H7NegRest_ok : CutTop4H7NegRestTree.geometryOK CutTop4H7NegPowerCache CutTop4H7NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutTop4H7NegRestPart0_ok) (RatioRemainder.geometryCut_ok (CutTop4H7NegRestPart1_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutTop4H7NegRestPart2_ok) (RatioRemainder.geometryCut_ok (CutTop4H7NegRestPart3_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutTop4H7NegRestPart4_ok) (CutTop4H7NegRestPart5_ok)) (CutTop4H7NegRestPart6_ok)) (CutTop4H7NegRestPart7_ok)))) (CutTop4H7NegRestPart8_ok)))) (CutTop4H7NegRestPart9_ok)

end HlawkaSchatten.BelowExponent.G3P
