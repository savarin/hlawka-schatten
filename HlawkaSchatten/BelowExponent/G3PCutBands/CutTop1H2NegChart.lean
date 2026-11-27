/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H2NegChartPart5

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H2NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H2NegChartBox : Box := ⟨![9/68, 4/25, 0, -1], ![27/136, 17/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop1H2NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop1H2NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop1H2NegChartPart1Tree) (.cut 2 (5/16) (CutTop1H2NegChartPart2Tree) (CutTop1H2NegChartPart3Tree))) (CutTop1H2NegChartPart4Tree))) (CutTop1H2NegChartPart5Tree)

set_option maxRecDepth 16000 in
theorem CutTop1H2NegChart_ok : CutTop1H2NegChartTree.ok CutTop1H2NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop1H2NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop1H2NegChartPart1_ok) (RatioChart.cut_ok (CutTop1H2NegChartPart2_ok) (CutTop1H2NegChartPart3_ok))) (CutTop1H2NegChartPart4_ok))) (CutTop1H2NegChartPart5_ok)

end HlawkaSchatten.BelowExponent.G3P
