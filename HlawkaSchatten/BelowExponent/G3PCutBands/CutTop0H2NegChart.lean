/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H2NegChartPart3

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H2NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H2NegChartBox : Box := ⟨![9/68, 3/20, 0, -1], ![27/136, 4/25, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop0H2NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop0H2NegChartPart0Tree) (.cut 2 (1/2) (CutTop0H2NegChartPart1Tree) (CutTop0H2NegChartPart2Tree))) (CutTop0H2NegChartPart3Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H2NegChart_ok : CutTop0H2NegChartTree.geometryOK CutTop0H2NegPowerCache CutTop0H2NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop0H2NegChartPart0_ok) (RatioChart.geometryCut_ok (CutTop0H2NegChartPart1_ok) (CutTop0H2NegChartPart2_ok))) (CutTop0H2NegChartPart3_ok)

end HlawkaSchatten.BelowExponent.G3P
