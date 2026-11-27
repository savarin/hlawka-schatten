/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H4NegChartPart5

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H4NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H4NegChartBox : Box := ⟨![9/34, 3/20, 0, -1], ![45/136, 4/25, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop0H4NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop0H4NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop0H4NegChartPart1Tree) (.cut 2 (5/16) (CutTop0H4NegChartPart2Tree) (CutTop0H4NegChartPart3Tree))) (CutTop0H4NegChartPart4Tree))) (CutTop0H4NegChartPart5Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H4NegChart_ok : CutTop0H4NegChartTree.ok CutTop0H4NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop0H4NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop0H4NegChartPart1_ok) (RatioChart.cut_ok (CutTop0H4NegChartPart2_ok) (CutTop0H4NegChartPart3_ok))) (CutTop0H4NegChartPart4_ok))) (CutTop0H4NegChartPart5_ok)

end HlawkaSchatten.BelowExponent.G3P
