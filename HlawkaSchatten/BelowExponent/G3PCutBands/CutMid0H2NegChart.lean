/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H2NegChartPart4

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H2NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H2NegChartBox : Box := ⟨![9/34, 1/20, 0, -1], ![27/68, 7/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutMid0H2NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutMid0H2NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid0H2NegChartPart1Tree) (CutMid0H2NegChartPart2Tree)) (CutMid0H2NegChartPart3Tree))) (CutMid0H2NegChartPart4Tree)

set_option maxRecDepth 16000 in
theorem CutMid0H2NegChart_ok : CutMid0H2NegChartTree.ok CutMid0H2NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutMid0H2NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutMid0H2NegChartPart1_ok) (CutMid0H2NegChartPart2_ok)) (CutMid0H2NegChartPart3_ok))) (CutMid0H2NegChartPart4_ok)

end HlawkaSchatten.BelowExponent.G3P
