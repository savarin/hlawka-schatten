/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H2NegChartPart12

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H2NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H2NegChartBox : Box := ⟨![9/34, 13/100, 0, -1], ![27/68, 3/20, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutMid4H2NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutMid4H2NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid4H2NegChartPart1Tree) (.cut 2 (5/16) (.cut 0 (45/136) (.cut 1 (7/50) (CutMid4H2NegChartPart2Tree) (CutMid4H2NegChartPart3Tree)) (.cut 3 (0) (.cut 3 (-1/8) (CutMid4H2NegChartPart4Tree) (CutMid4H2NegChartPart5Tree)) (CutMid4H2NegChartPart6Tree))) (.cut 3 (0) (.cut 3 (-1/8) (CutMid4H2NegChartPart7Tree) (.cut 0 (45/136) (CutMid4H2NegChartPart8Tree) (CutMid4H2NegChartPart9Tree))) (CutMid4H2NegChartPart10Tree)))) (CutMid4H2NegChartPart11Tree))) (CutMid4H2NegChartPart12Tree)

set_option maxRecDepth 16000 in
theorem CutMid4H2NegChart_ok : CutMid4H2NegChartTree.ok CutMid4H2NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutMid4H2NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutMid4H2NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutMid4H2NegChartPart2_ok) (CutMid4H2NegChartPart3_ok)) (RatioChart.cut_ok (RatioChart.cut_ok (CutMid4H2NegChartPart4_ok) (CutMid4H2NegChartPart5_ok)) (CutMid4H2NegChartPart6_ok))) (RatioChart.cut_ok (RatioChart.cut_ok (CutMid4H2NegChartPart7_ok) (RatioChart.cut_ok (CutMid4H2NegChartPart8_ok) (CutMid4H2NegChartPart9_ok))) (CutMid4H2NegChartPart10_ok)))) (CutMid4H2NegChartPart11_ok))) (CutMid4H2NegChartPart12_ok)

end HlawkaSchatten.BelowExponent.G3P
