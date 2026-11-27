/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegRestPart19

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H2NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H2NegRestBox : Box := ⟨![9/34, 9/100, 0, -8], ![27/68, 11/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid2H2NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid2H2NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (CutMid2H2NegRestPart1Tree) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (1/10) (.cut 1 (19/200) (CutMid2H2NegRestPart2Tree) (.cut 0 (45/136) (CutMid2H2NegRestPart3Tree) (.cut 1 (39/400) (CutMid2H2NegRestPart4Tree) (CutMid2H2NegRestPart5Tree)))) (.cut 1 (21/200) (.cut 0 (45/136) (.cut 1 (41/400) (CutMid2H2NegRestPart6Tree) (CutMid2H2NegRestPart7Tree)) (.cut 3 (1/32) (CutMid2H2NegRestPart8Tree) (CutMid2H2NegRestPart9Tree))) (.cut 0 (45/136) (.cut 1 (43/400) (CutMid2H2NegRestPart10Tree) (CutMid2H2NegRestPart11Tree)) (.cut 3 (1/32) (CutMid2H2NegRestPart12Tree) (CutMid2H2NegRestPart13Tree))))) (CutMid2H2NegRestPart14Tree)) (CutMid2H2NegRestPart15Tree))) (CutMid2H2NegRestPart16Tree)) (CutMid2H2NegRestPart17Tree)) (CutMid2H2NegRestPart18Tree))) (CutMid2H2NegRestPart19Tree)

set_option maxRecDepth 16000 in
theorem CutMid2H2NegRest_ok : CutMid2H2NegRestTree.geometryOK CutMid2H2NegPowerCache CutMid2H2NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H2NegRestPart0_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H2NegRestPart1_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H2NegRestPart2_ok) (RatioRemainder.geometryCut_ok (CutMid2H2NegRestPart3_ok) (RatioRemainder.geometryCut_ok (CutMid2H2NegRestPart4_ok) (CutMid2H2NegRestPart5_ok)))) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H2NegRestPart6_ok) (CutMid2H2NegRestPart7_ok)) (RatioRemainder.geometryCut_ok (CutMid2H2NegRestPart8_ok) (CutMid2H2NegRestPart9_ok))) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H2NegRestPart10_ok) (CutMid2H2NegRestPart11_ok)) (RatioRemainder.geometryCut_ok (CutMid2H2NegRestPart12_ok) (CutMid2H2NegRestPart13_ok))))) (CutMid2H2NegRestPart14_ok)) (CutMid2H2NegRestPart15_ok))) (CutMid2H2NegRestPart16_ok)) (CutMid2H2NegRestPart17_ok)) (CutMid2H2NegRestPart18_ok))) (CutMid2H2NegRestPart19_ok)

end HlawkaSchatten.BelowExponent.G3P
