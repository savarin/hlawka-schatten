/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H3NegChartPart1

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegChartBox : Box := ⟨![27/68, 7/100, 0, -1], ![9/17, 9/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutMid1H3NegChartTree : RatioChart :=
  .cut 3 (1/4) (CutMid1H3NegChartPart0Tree) (CutMid1H3NegChartPart1Tree)

set_option maxRecDepth 16000 in
theorem CutMid1H3NegChart_ok : CutMid1H3NegChartTree.ok CutMid1H3NegChartBox false = true :=
  RatioChart.cut_ok (CutMid1H3NegChartPart0_ok) (CutMid1H3NegChartPart1_ok)

end HlawkaSchatten.BelowExponent.G3P
