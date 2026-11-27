/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegChartPart10

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H1NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H1NegChartBox : Box := ⟨![9/136, 9/50, 0, -1], ![9/68, 19/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop3H1NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop3H1NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H1NegChartPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (CutTop3H1NegChartPart2Tree) (.cut 0 (27/272) (CutTop3H1NegChartPart3Tree) (CutTop3H1NegChartPart4Tree))) (.cut 3 (0) (CutTop3H1NegChartPart5Tree) (.cut 3 (1/8) (.cut 3 (1/16) (CutTop3H1NegChartPart6Tree) (CutTop3H1NegChartPart7Tree)) (CutTop3H1NegChartPart8Tree))))) (CutTop3H1NegChartPart9Tree))) (CutTop3H1NegChartPart10Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H1NegChart_ok : CutTop3H1NegChartTree.ok CutTop3H1NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H1NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H1NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H1NegChartPart2_ok) (RatioChart.cut_ok (CutTop3H1NegChartPart3_ok) (CutTop3H1NegChartPart4_ok))) (RatioChart.cut_ok (CutTop3H1NegChartPart5_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H1NegChartPart6_ok) (CutTop3H1NegChartPart7_ok)) (CutTop3H1NegChartPart8_ok))))) (CutTop3H1NegChartPart9_ok))) (CutTop3H1NegChartPart10_ok)

end HlawkaSchatten.BelowExponent.G3P
