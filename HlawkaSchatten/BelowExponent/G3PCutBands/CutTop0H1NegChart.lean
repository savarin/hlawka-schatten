/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H1NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H1NegChartPart1

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H1NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H1NegChartBox : Box := ⟨![9/136, 3/20, 0, -1], ![9/68, 4/25, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop0H1NegChartTree : RatioChart :=
  .cut 3 (1/4) (CutTop0H1NegChartPart0Tree) (CutTop0H1NegChartPart1Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H1NegChart_ok : CutTop0H1NegChartTree.geometryOK CutTop0H1NegPowerCache CutTop0H1NegChartBox false = true :=
  RatioChart.geometryCut_ok (CutTop0H1NegChartPart0_ok) (CutTop0H1NegChartPart1_ok)

end HlawkaSchatten.BelowExponent.G3P
