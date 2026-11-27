/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegChartPart14

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H2NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H2NegChartBox : Box := ⟨![9/68, 9/50, 0, -1], ![27/136, 19/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop3H2NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop3H2NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H2NegChartPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop3H2NegChartPart2Tree) (.cut 3 (-1/16) (CutTop3H2NegChartPart3Tree) (CutTop3H2NegChartPart4Tree))) (CutTop3H2NegChartPart5Tree)) (.cut 3 (0) (.cut 3 (-1/8) (CutTop3H2NegChartPart6Tree) (.cut 3 (-1/16) (CutTop3H2NegChartPart7Tree) (.cut 3 (-1/32) (CutTop3H2NegChartPart8Tree) (CutTop3H2NegChartPart9Tree)))) (.cut 3 (1/8) (.cut 3 (1/16) (CutTop3H2NegChartPart10Tree) (CutTop3H2NegChartPart11Tree)) (CutTop3H2NegChartPart12Tree))))) (CutTop3H2NegChartPart13Tree))) (CutTop3H2NegChartPart14Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H2NegChart_ok : CutTop3H2NegChartTree.ok CutTop3H2NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H2NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H2NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H2NegChartPart2_ok) (RatioChart.cut_ok (CutTop3H2NegChartPart3_ok) (CutTop3H2NegChartPart4_ok))) (CutTop3H2NegChartPart5_ok)) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H2NegChartPart6_ok) (RatioChart.cut_ok (CutTop3H2NegChartPart7_ok) (RatioChart.cut_ok (CutTop3H2NegChartPart8_ok) (CutTop3H2NegChartPart9_ok)))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop3H2NegChartPart10_ok) (CutTop3H2NegChartPart11_ok)) (CutTop3H2NegChartPart12_ok))))) (CutTop3H2NegChartPart13_ok))) (CutTop3H2NegChartPart14_ok)

end HlawkaSchatten.BelowExponent.G3P
