/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegRestPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegRestPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegRestPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegRestPart9

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0NegRestBox : Box := ⟨![0, 9/100, 0, -8], ![9/68, 11/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid2H0NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid2H0NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid2H0NegRestPart1Tree) (.cut 3 (1/8) (.cut 1 (1/10) (CutMid2H0NegRestPart2Tree) (.cut 1 (21/200) (CutMid2H0NegRestPart3Tree) (CutMid2H0NegRestPart4Tree))) (CutMid2H0NegRestPart5Tree))) (CutMid2H0NegRestPart6Tree)) (CutMid2H0NegRestPart7Tree)) (CutMid2H0NegRestPart8Tree))) (CutMid2H0NegRestPart9Tree)

set_option maxRecDepth 16000 in
theorem CutMid2H0NegRest_ok : CutMid2H0NegRestTree.geometryOK CutMid2H0NegPowerCache CutMid2H0NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H0NegRestPart0_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H0NegRestPart1_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H0NegRestPart2_ok) (RatioRemainder.geometryCut_ok (CutMid2H0NegRestPart3_ok) (CutMid2H0NegRestPart4_ok))) (CutMid2H0NegRestPart5_ok))) (CutMid2H0NegRestPart6_ok)) (CutMid2H0NegRestPart7_ok)) (CutMid2H0NegRestPart8_ok))) (CutMid2H0NegRestPart9_ok)

end HlawkaSchatten.BelowExponent.G3P
