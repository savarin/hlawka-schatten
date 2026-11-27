/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H3NegChartPart10

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3NegChartBox : Box := ⟨![27/68, 13/100, 0, -1], ![9/17, 3/20, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutMid4H3NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutMid4H3NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid4H3NegChartPart1Tree) (.cut 2 (5/16) (.cut 1 (7/50) (CutMid4H3NegChartPart2Tree) (.cut 0 (63/136) (CutMid4H3NegChartPart3Tree) (CutMid4H3NegChartPart4Tree))) (.cut 3 (0) (.cut 3 (-1/8) (CutMid4H3NegChartPart5Tree) (.cut 0 (63/136) (CutMid4H3NegChartPart6Tree) (CutMid4H3NegChartPart7Tree))) (CutMid4H3NegChartPart8Tree)))) (CutMid4H3NegChartPart9Tree))) (CutMid4H3NegChartPart10Tree)

set_option maxRecDepth 16000 in
theorem CutMid4H3NegChart_ok : CutMid4H3NegChartTree.ok CutMid4H3NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutMid4H3NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutMid4H3NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutMid4H3NegChartPart2_ok) (RatioChart.cut_ok (CutMid4H3NegChartPart3_ok) (CutMid4H3NegChartPart4_ok))) (RatioChart.cut_ok (RatioChart.cut_ok (CutMid4H3NegChartPart5_ok) (RatioChart.cut_ok (CutMid4H3NegChartPart6_ok) (CutMid4H3NegChartPart7_ok))) (CutMid4H3NegChartPart8_ok)))) (CutMid4H3NegChartPart9_ok))) (CutMid4H3NegChartPart10_ok)

end HlawkaSchatten.BelowExponent.G3P
