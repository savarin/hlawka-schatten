/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H3NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H3NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H3NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H3NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H3NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H3NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H3NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H3NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H3NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H3NegChartPart9

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H3NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H3NegChartBox : Box := ⟨![27/136, 17/100, 0, -1], ![9/34, 9/50, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop2H3NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop2H3NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop2H3NegChartPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (CutTop2H3NegChartPart2Tree) (CutTop2H3NegChartPart3Tree)) (.cut 3 (0) (.cut 3 (-1/8) (CutTop2H3NegChartPart4Tree) (.cut 3 (-1/16) (CutTop2H3NegChartPart5Tree) (CutTop2H3NegChartPart6Tree))) (CutTop2H3NegChartPart7Tree)))) (CutTop2H3NegChartPart8Tree))) (CutTop2H3NegChartPart9Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H3NegChart_ok : CutTop2H3NegChartTree.ok CutTop2H3NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop2H3NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop2H3NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop2H3NegChartPart2_ok) (CutTop2H3NegChartPart3_ok)) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop2H3NegChartPart4_ok) (RatioChart.cut_ok (CutTop2H3NegChartPart5_ok) (CutTop2H3NegChartPart6_ok))) (CutTop2H3NegChartPart7_ok)))) (CutTop2H3NegChartPart8_ok))) (CutTop2H3NegChartPart9_ok)

end HlawkaSchatten.BelowExponent.G3P
