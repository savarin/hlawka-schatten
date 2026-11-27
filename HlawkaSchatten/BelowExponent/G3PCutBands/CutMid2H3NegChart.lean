/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H3NegChartPart4

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H3NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H3NegChartBox : Box := ⟨![27/68, 9/100, 0, -1], ![9/17, 11/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutMid2H3NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutMid2H3NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid2H3NegChartPart1Tree) (CutMid2H3NegChartPart2Tree)) (CutMid2H3NegChartPart3Tree))) (CutMid2H3NegChartPart4Tree)

set_option maxRecDepth 16000 in
theorem CutMid2H3NegChart_ok : CutMid2H3NegChartTree.ok CutMid2H3NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutMid2H3NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutMid2H3NegChartPart1_ok) (CutMid2H3NegChartPart2_ok)) (CutMid2H3NegChartPart3_ok))) (CutMid2H3NegChartPart4_ok)

end HlawkaSchatten.BelowExponent.G3P
