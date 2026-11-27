/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegRestPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegRestPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegRestPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegRestPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegRestPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegRestPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegRestPart12

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1NegRestBox : Box := ⟨![9/68, 9/100, 0, -8], ![9/34, 11/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid2H1NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid2H1NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid2H1NegRestPart1Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (1/10) (CutMid2H1NegRestPart2Tree) (.cut 1 (21/200) (.cut 0 (27/136) (CutMid2H1NegRestPart3Tree) (CutMid2H1NegRestPart4Tree)) (.cut 0 (27/136) (CutMid2H1NegRestPart5Tree) (CutMid2H1NegRestPart6Tree)))) (CutMid2H1NegRestPart7Tree)) (CutMid2H1NegRestPart8Tree))) (CutMid2H1NegRestPart9Tree)) (CutMid2H1NegRestPart10Tree)) (CutMid2H1NegRestPart11Tree))) (CutMid2H1NegRestPart12Tree)

set_option maxRecDepth 16000 in
theorem CutMid2H1NegRest_ok : CutMid2H1NegRestTree.geometryOK CutMid2H1NegPowerCache CutMid2H1NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H1NegRestPart0_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H1NegRestPart1_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H1NegRestPart2_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H1NegRestPart3_ok) (CutMid2H1NegRestPart4_ok)) (RatioRemainder.geometryCut_ok (CutMid2H1NegRestPart5_ok) (CutMid2H1NegRestPart6_ok)))) (CutMid2H1NegRestPart7_ok)) (CutMid2H1NegRestPart8_ok))) (CutMid2H1NegRestPart9_ok)) (CutMid2H1NegRestPart10_ok)) (CutMid2H1NegRestPart11_ok))) (CutMid2H1NegRestPart12_ok)

end HlawkaSchatten.BelowExponent.G3P
