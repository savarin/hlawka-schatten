/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H7NegChartPart6

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H7NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H7NegChartBox : Box := ⟨![63/136, 3/20, 0, -1], ![9/17, 4/25, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop0H7NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop0H7NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop0H7NegChartPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (CutTop0H7NegChartPart2Tree) (CutTop0H7NegChartPart3Tree)) (CutTop0H7NegChartPart4Tree))) (CutTop0H7NegChartPart5Tree))) (CutTop0H7NegChartPart6Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H7NegChart_ok : CutTop0H7NegChartTree.ok CutTop0H7NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop0H7NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop0H7NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop0H7NegChartPart2_ok) (CutTop0H7NegChartPart3_ok)) (CutTop0H7NegChartPart4_ok))) (CutTop0H7NegChartPart5_ok))) (CutTop0H7NegChartPart6_ok)

end HlawkaSchatten.BelowExponent.G3P
