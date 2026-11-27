/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegRestPart24

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegRestBox : Box := ⟨![27/68, 9/100, 0, -8], ![9/17, 11/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid2H3NegRestTree : RatioRemainder :=
  .cut 3 (3/4) (.cut 3 (-1/4) (CutMid2H3NegRestPart0Tree) (.cut 3 (1/4) (.cut 2 (1/2) (.cut 2 (1/8) (.cut 3 (0) (.cut 1 (1/10) (.cut 1 (19/200) (.cut 3 (-1/8) (CutMid2H3NegRestPart1Tree) (.cut 0 (63/136) (CutMid2H3NegRestPart2Tree) (CutMid2H3NegRestPart3Tree))) (.cut 3 (-1/8) (CutMid2H3NegRestPart4Tree) (.cut 0 (63/136) (CutMid2H3NegRestPart5Tree) (CutMid2H3NegRestPart6Tree)))) (.cut 1 (21/200) (.cut 3 (-1/8) (CutMid2H3NegRestPart7Tree) (.cut 0 (63/136) (CutMid2H3NegRestPart8Tree) (CutMid2H3NegRestPart9Tree))) (CutMid2H3NegRestPart10Tree))) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 1 (1/10) (.cut 3 (1/32) (.cut 1 (19/200) (.cut 0 (63/136) (CutMid2H3NegRestPart11Tree) (CutMid2H3NegRestPart12Tree)) (.cut 0 (63/136) (CutMid2H3NegRestPart13Tree) (CutMid2H3NegRestPart14Tree))) (CutMid2H3NegRestPart15Tree)) (.cut 3 (1/32) (.cut 1 (21/200) (CutMid2H3NegRestPart16Tree) (CutMid2H3NegRestPart17Tree)) (CutMid2H3NegRestPart18Tree))) (CutMid2H3NegRestPart19Tree)) (CutMid2H3NegRestPart20Tree))) (CutMid2H3NegRestPart21Tree)) (CutMid2H3NegRestPart22Tree)) (CutMid2H3NegRestPart23Tree))) (CutMid2H3NegRestPart24Tree)

set_option maxRecDepth 16000 in
theorem CutMid2H3NegRest_ok : CutMid2H3NegRestTree.geometryOK CutMid2H3NegPowerCache CutMid2H3NegRestBox false (1) = true :=
  RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H3NegRestPart0_ok) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H3NegRestPart1_ok) (RatioRemainder.geometryCut_ok (CutMid2H3NegRestPart2_ok) (CutMid2H3NegRestPart3_ok))) (RatioRemainder.geometryCut_ok (CutMid2H3NegRestPart4_ok) (RatioRemainder.geometryCut_ok (CutMid2H3NegRestPart5_ok) (CutMid2H3NegRestPart6_ok)))) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H3NegRestPart7_ok) (RatioRemainder.geometryCut_ok (CutMid2H3NegRestPart8_ok) (CutMid2H3NegRestPart9_ok))) (CutMid2H3NegRestPart10_ok))) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H3NegRestPart11_ok) (CutMid2H3NegRestPart12_ok)) (RatioRemainder.geometryCut_ok (CutMid2H3NegRestPart13_ok) (CutMid2H3NegRestPart14_ok))) (CutMid2H3NegRestPart15_ok)) (RatioRemainder.geometryCut_ok (RatioRemainder.geometryCut_ok (CutMid2H3NegRestPart16_ok) (CutMid2H3NegRestPart17_ok)) (CutMid2H3NegRestPart18_ok))) (CutMid2H3NegRestPart19_ok)) (CutMid2H3NegRestPart20_ok))) (CutMid2H3NegRestPart21_ok)) (CutMid2H3NegRestPart22_ok)) (CutMid2H3NegRestPart23_ok))) (CutMid2H3NegRestPart24_ok)

end HlawkaSchatten.BelowExponent.G3P
