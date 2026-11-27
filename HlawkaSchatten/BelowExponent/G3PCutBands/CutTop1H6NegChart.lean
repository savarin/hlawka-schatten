/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H6NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H6NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H6NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H6NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H6NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H6NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H6NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H6NegChartPart7

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H6NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H6NegChartBox : Box := ⟨![27/68, 4/25, 0, -1], ![63/136, 17/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop1H6NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop1H6NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop1H6NegChartPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (CutTop1H6NegChartPart2Tree) (.cut 3 (-1/16) (CutTop1H6NegChartPart3Tree) (CutTop1H6NegChartPart4Tree))) (CutTop1H6NegChartPart5Tree))) (CutTop1H6NegChartPart6Tree))) (CutTop1H6NegChartPart7Tree)

set_option maxRecDepth 16000 in
theorem CutTop1H6NegChart_ok : CutTop1H6NegChartTree.ok CutTop1H6NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop1H6NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop1H6NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop1H6NegChartPart2_ok) (RatioChart.cut_ok (CutTop1H6NegChartPart3_ok) (CutTop1H6NegChartPart4_ok))) (CutTop1H6NegChartPart5_ok))) (CutTop1H6NegChartPart6_ok))) (CutTop1H6NegChartPart7_ok)

end HlawkaSchatten.BelowExponent.G3P
