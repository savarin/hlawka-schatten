/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H5NegChartPart5

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H5NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H5NegChartBox : Box := ⟨![45/136, 3/20, 0, -1], ![27/68, 4/25, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop0H5NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop0H5NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop0H5NegChartPart1Tree) (.cut 2 (5/16) (CutTop0H5NegChartPart2Tree) (CutTop0H5NegChartPart3Tree))) (CutTop0H5NegChartPart4Tree))) (CutTop0H5NegChartPart5Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H5NegChart_ok : CutTop0H5NegChartTree.ok CutTop0H5NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop0H5NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop0H5NegChartPart1_ok) (RatioChart.cut_ok (CutTop0H5NegChartPart2_ok) (CutTop0H5NegChartPart3_ok))) (CutTop0H5NegChartPart4_ok))) (CutTop0H5NegChartPart5_ok)

end HlawkaSchatten.BelowExponent.G3P
