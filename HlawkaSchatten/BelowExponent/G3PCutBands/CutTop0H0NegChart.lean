/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H0NegChartPart2

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H0NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H0NegChartBox : Box := ⟨![0, 3/20, 0, -1], ![9/136, 4/25, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop0H0NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop0H0NegChartPart0Tree) (CutTop0H0NegChartPart1Tree)) (CutTop0H0NegChartPart2Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H0NegChart_ok : CutTop0H0NegChartTree.geometryOK CutTop0H0NegPowerCache CutTop0H0NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop0H0NegChartPart0_ok) (CutTop0H0NegChartPart1_ok)) (CutTop0H0NegChartPart2_ok)

end HlawkaSchatten.BelowExponent.G3P
