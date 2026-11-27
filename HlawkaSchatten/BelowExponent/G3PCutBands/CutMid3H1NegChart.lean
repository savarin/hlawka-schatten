/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegChartPart6

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H1NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H1NegChartBox : Box := ⟨![9/68, 11/100, 0, -1], ![9/34, 13/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutMid3H1NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutMid3H1NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid3H1NegChartPart1Tree) (.cut 2 (5/16) (.cut 1 (3/25) (CutMid3H1NegChartPart2Tree) (CutMid3H1NegChartPart3Tree)) (CutMid3H1NegChartPart4Tree))) (CutMid3H1NegChartPart5Tree))) (CutMid3H1NegChartPart6Tree)

set_option maxRecDepth 16000 in
theorem CutMid3H1NegChart_ok : CutMid3H1NegChartTree.ok CutMid3H1NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutMid3H1NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutMid3H1NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutMid3H1NegChartPart2_ok) (CutMid3H1NegChartPart3_ok)) (CutMid3H1NegChartPart4_ok))) (CutMid3H1NegChartPart5_ok))) (CutMid3H1NegChartPart6_ok)

end HlawkaSchatten.BelowExponent.G3P
