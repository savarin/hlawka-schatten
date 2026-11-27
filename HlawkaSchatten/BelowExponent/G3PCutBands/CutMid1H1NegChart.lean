/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegChartPart7

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H1NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H1NegChartBox : Box := ⟨![9/68, 7/100, 0, -1], ![9/34, 9/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutMid1H1NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutMid1H1NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid1H1NegChartPart1Tree) (.cut 2 (5/16) (.cut 2 (7/32) (.cut 1 (2/25) (CutMid1H1NegChartPart2Tree) (CutMid1H1NegChartPart3Tree)) (CutMid1H1NegChartPart4Tree)) (CutMid1H1NegChartPart5Tree))) (CutMid1H1NegChartPart6Tree))) (CutMid1H1NegChartPart7Tree)

set_option maxRecDepth 16000 in
theorem CutMid1H1NegChart_ok : CutMid1H1NegChartTree.ok CutMid1H1NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutMid1H1NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutMid1H1NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutMid1H1NegChartPart2_ok) (CutMid1H1NegChartPart3_ok)) (CutMid1H1NegChartPart4_ok)) (CutMid1H1NegChartPart5_ok))) (CutMid1H1NegChartPart6_ok))) (CutMid1H1NegChartPart7_ok)

end HlawkaSchatten.BelowExponent.G3P
