/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H1NegChartPart7

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H1NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H1NegChartBox : Box := ⟨![9/136, 17/100, 0, -1], ![9/68, 9/50, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop2H1NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop2H1NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop2H1NegChartPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (CutTop2H1NegChartPart2Tree) (CutTop2H1NegChartPart3Tree)) (.cut 3 (0) (CutTop2H1NegChartPart4Tree) (CutTop2H1NegChartPart5Tree)))) (CutTop2H1NegChartPart6Tree))) (CutTop2H1NegChartPart7Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H1NegChart_ok : CutTop2H1NegChartTree.ok CutTop2H1NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop2H1NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop2H1NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop2H1NegChartPart2_ok) (CutTop2H1NegChartPart3_ok)) (RatioChart.cut_ok (CutTop2H1NegChartPart4_ok) (CutTop2H1NegChartPart5_ok)))) (CutTop2H1NegChartPart6_ok))) (CutTop2H1NegChartPart7_ok)

end HlawkaSchatten.BelowExponent.G3P
