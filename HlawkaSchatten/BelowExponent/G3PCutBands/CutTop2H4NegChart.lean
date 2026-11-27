/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegChartPart10

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H4NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H4NegChartBox : Box := ⟨![9/34, 17/100, 0, -1], ![45/136, 9/50, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop2H4NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop2H4NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop2H4NegChartPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop2H4NegChartPart2Tree) (CutTop2H4NegChartPart3Tree)) (CutTop2H4NegChartPart4Tree)) (.cut 3 (0) (.cut 3 (-1/8) (CutTop2H4NegChartPart5Tree) (.cut 3 (-1/16) (CutTop2H4NegChartPart6Tree) (CutTop2H4NegChartPart7Tree))) (CutTop2H4NegChartPart8Tree)))) (CutTop2H4NegChartPart9Tree))) (CutTop2H4NegChartPart10Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H4NegChart_ok : CutTop2H4NegChartTree.ok CutTop2H4NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop2H4NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop2H4NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop2H4NegChartPart2_ok) (CutTop2H4NegChartPart3_ok)) (CutTop2H4NegChartPart4_ok)) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop2H4NegChartPart5_ok) (RatioChart.cut_ok (CutTop2H4NegChartPart6_ok) (CutTop2H4NegChartPart7_ok))) (CutTop2H4NegChartPart8_ok)))) (CutTop2H4NegChartPart9_ok))) (CutTop2H4NegChartPart10_ok)

end HlawkaSchatten.BelowExponent.G3P
