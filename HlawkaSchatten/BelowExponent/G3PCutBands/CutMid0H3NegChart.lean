/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid0H3NegChartPart2

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H3NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H3NegChartBox : Box := ⟨![27/68, 1/20, 0, -1], ![9/17, 7/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutMid0H3NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutMid0H3NegChartPart0Tree) (CutMid0H3NegChartPart1Tree)) (CutMid0H3NegChartPart2Tree)

set_option maxRecDepth 16000 in
theorem CutMid0H3NegChart_ok : CutMid0H3NegChartTree.geometryOK CutMid0H3NegPowerCache CutMid0H3NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid0H3NegChartPart0_ok) (CutMid0H3NegChartPart1_ok)) (CutMid0H3NegChartPart2_ok)

end HlawkaSchatten.BelowExponent.G3P
