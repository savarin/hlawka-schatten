/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegChartPart14

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H0NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H0NegChartBox : Box := ⟨![0, 9/50, 0, -1], ![9/136, 19/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop3H0NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop3H0NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H0NegChartPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (CutTop3H0NegChartPart2Tree) (.cut 0 (9/272) (CutTop3H0NegChartPart3Tree) (CutTop3H0NegChartPart4Tree))) (.cut 3 (0) (CutTop3H0NegChartPart5Tree) (.cut 2 (13/32) (.cut 0 (9/272) (CutTop3H0NegChartPart6Tree) (CutTop3H0NegChartPart7Tree)) (CutTop3H0NegChartPart8Tree))))) (CutTop3H0NegChartPart9Tree))) (.cut 3 (3/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H0NegChartPart10Tree) (.cut 2 (5/16) (CutTop3H0NegChartPart11Tree) (CutTop3H0NegChartPart12Tree))) (CutTop3H0NegChartPart13Tree)) (CutTop3H0NegChartPart14Tree))

set_option maxRecDepth 16000 in
theorem CutTop3H0NegChart_ok : CutTop3H0NegChartTree.ok CutTop3H0NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H0NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H0NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H0NegChartPart2_ok) (RatioChart.cut_ok (CutTop3H0NegChartPart3_ok) (CutTop3H0NegChartPart4_ok))) (RatioChart.cut_ok (CutTop3H0NegChartPart5_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H0NegChartPart6_ok) (CutTop3H0NegChartPart7_ok)) (CutTop3H0NegChartPart8_ok))))) (CutTop3H0NegChartPart9_ok))) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H0NegChartPart10_ok) (RatioChart.cut_ok (CutTop3H0NegChartPart11_ok) (CutTop3H0NegChartPart12_ok))) (CutTop3H0NegChartPart13_ok)) (CutTop3H0NegChartPart14_ok))

end HlawkaSchatten.BelowExponent.G3P
