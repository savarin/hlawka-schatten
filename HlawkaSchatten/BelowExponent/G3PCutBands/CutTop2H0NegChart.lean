/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H0NegChartPart7

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H0NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H0NegChartBox : Box := ⟨![0, 17/100, 0, -1], ![9/136, 9/50, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop2H0NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop2H0NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop2H0NegChartPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (CutTop2H0NegChartPart2Tree) (.cut 0 (9/272) (CutTop2H0NegChartPart3Tree) (CutTop2H0NegChartPart4Tree))) (CutTop2H0NegChartPart5Tree))) (CutTop2H0NegChartPart6Tree))) (CutTop2H0NegChartPart7Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H0NegChart_ok : CutTop2H0NegChartTree.ok CutTop2H0NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop2H0NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop2H0NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop2H0NegChartPart2_ok) (RatioChart.cut_ok (CutTop2H0NegChartPart3_ok) (CutTop2H0NegChartPart4_ok))) (CutTop2H0NegChartPart5_ok))) (CutTop2H0NegChartPart6_ok))) (CutTop2H0NegChartPart7_ok)

end HlawkaSchatten.BelowExponent.G3P
