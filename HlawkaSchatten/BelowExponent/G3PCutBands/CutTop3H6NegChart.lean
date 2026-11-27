/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegChartPart12

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H6NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H6NegChartBox : Box := ⟨![27/68, 9/50, 0, -1], ![63/136, 19/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop3H6NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop3H6NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H6NegChartPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (.cut 2 (5/16) (CutTop3H6NegChartPart2Tree) (CutTop3H6NegChartPart3Tree)) (.cut 3 (-1/16) (.cut 2 (5/16) (CutTop3H6NegChartPart4Tree) (.cut 0 (117/272) (CutTop3H6NegChartPart5Tree) (CutTop3H6NegChartPart6Tree))) (.cut 2 (5/16) (CutTop3H6NegChartPart7Tree) (.cut 3 (-1/32) (CutTop3H6NegChartPart8Tree) (CutTop3H6NegChartPart9Tree))))) (CutTop3H6NegChartPart10Tree))) (CutTop3H6NegChartPart11Tree))) (CutTop3H6NegChartPart12Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H6NegChart_ok : CutTop3H6NegChartTree.geometryOK CutTop3H6NegPowerCache CutTop3H6NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop3H6NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop3H6NegChartPart1_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop3H6NegChartPart2_ok) (CutTop3H6NegChartPart3_ok)) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop3H6NegChartPart4_ok) (RatioChart.geometryCut_ok (CutTop3H6NegChartPart5_ok) (CutTop3H6NegChartPart6_ok))) (RatioChart.geometryCut_ok (CutTop3H6NegChartPart7_ok) (RatioChart.geometryCut_ok (CutTop3H6NegChartPart8_ok) (CutTop3H6NegChartPart9_ok))))) (CutTop3H6NegChartPart10_ok))) (CutTop3H6NegChartPart11_ok))) (CutTop3H6NegChartPart12_ok)

end HlawkaSchatten.BelowExponent.G3P
