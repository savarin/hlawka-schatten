/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H3NegChartPart15

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H3NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H3NegChartBox : Box := ⟨![27/136, 9/50, 0, -1], ![9/34, 19/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop3H3NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop3H3NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H3NegChartPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop3H3NegChartPart2Tree) (.cut 3 (-1/16) (CutTop3H3NegChartPart3Tree) (CutTop3H3NegChartPart4Tree))) (CutTop3H3NegChartPart5Tree)) (.cut 3 (0) (.cut 3 (-1/8) (CutTop3H3NegChartPart6Tree) (.cut 3 (-1/16) (CutTop3H3NegChartPart7Tree) (.cut 3 (-1/32) (CutTop3H3NegChartPart8Tree) (.cut 0 (63/272) (CutTop3H3NegChartPart9Tree) (CutTop3H3NegChartPart10Tree))))) (.cut 3 (1/8) (.cut 3 (1/16) (CutTop3H3NegChartPart11Tree) (CutTop3H3NegChartPart12Tree)) (CutTop3H3NegChartPart13Tree))))) (CutTop3H3NegChartPart14Tree))) (CutTop3H3NegChartPart15Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H3NegChart_ok : CutTop3H3NegChartTree.ok CutTop3H3NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H3NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H3NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H3NegChartPart2_ok) (RatioChart.cut_ok (CutTop3H3NegChartPart3_ok) (CutTop3H3NegChartPart4_ok))) (CutTop3H3NegChartPart5_ok)) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H3NegChartPart6_ok) (RatioChart.cut_ok (CutTop3H3NegChartPart7_ok) (RatioChart.cut_ok (CutTop3H3NegChartPart8_ok) (RatioChart.cut_ok (CutTop3H3NegChartPart9_ok) (CutTop3H3NegChartPart10_ok))))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H3NegChartPart11_ok) (CutTop3H3NegChartPart12_ok)) (CutTop3H3NegChartPart13_ok))))) (CutTop3H3NegChartPart14_ok))) (CutTop3H3NegChartPart15_ok)

end HlawkaSchatten.BelowExponent.G3P
