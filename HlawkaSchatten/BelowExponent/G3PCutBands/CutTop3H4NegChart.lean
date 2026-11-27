/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegChartPart15

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H4NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H4NegChartBox : Box := ⟨![9/34, 9/50, 0, -1], ![45/136, 19/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop3H4NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop3H4NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H4NegChartPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop3H4NegChartPart2Tree) (.cut 3 (-1/16) (CutTop3H4NegChartPart3Tree) (CutTop3H4NegChartPart4Tree))) (CutTop3H4NegChartPart5Tree)) (.cut 3 (0) (.cut 3 (-1/8) (CutTop3H4NegChartPart6Tree) (.cut 3 (-1/16) (CutTop3H4NegChartPart7Tree) (.cut 3 (-1/32) (.cut 0 (81/272) (CutTop3H4NegChartPart8Tree) (CutTop3H4NegChartPart9Tree)) (.cut 0 (81/272) (CutTop3H4NegChartPart10Tree) (CutTop3H4NegChartPart11Tree))))) (.cut 3 (1/8) (CutTop3H4NegChartPart12Tree) (CutTop3H4NegChartPart13Tree))))) (CutTop3H4NegChartPart14Tree))) (CutTop3H4NegChartPart15Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H4NegChart_ok : CutTop3H4NegChartTree.geometryOK CutTop3H4NegPowerCache CutTop3H4NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop3H4NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop3H4NegChartPart1_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop3H4NegChartPart2_ok) (RatioChart.geometryCut_ok (CutTop3H4NegChartPart3_ok) (CutTop3H4NegChartPart4_ok))) (CutTop3H4NegChartPart5_ok)) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop3H4NegChartPart6_ok) (RatioChart.geometryCut_ok (CutTop3H4NegChartPart7_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop3H4NegChartPart8_ok) (CutTop3H4NegChartPart9_ok)) (RatioChart.geometryCut_ok (CutTop3H4NegChartPart10_ok) (CutTop3H4NegChartPart11_ok))))) (RatioChart.geometryCut_ok (CutTop3H4NegChartPart12_ok) (CutTop3H4NegChartPart13_ok))))) (CutTop3H4NegChartPart14_ok))) (CutTop3H4NegChartPart15_ok)

end HlawkaSchatten.BelowExponent.G3P
