/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H3NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H3NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H3NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H3NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H3NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop0H3NegChartPart5

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H3NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H3NegChartBox : Box := ⟨![27/136, 3/20, 0, -1], ![9/34, 4/25, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop0H3NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop0H3NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop0H3NegChartPart1Tree) (.cut 2 (5/16) (CutTop0H3NegChartPart2Tree) (CutTop0H3NegChartPart3Tree))) (CutTop0H3NegChartPart4Tree))) (CutTop0H3NegChartPart5Tree)

set_option maxRecDepth 16000 in
theorem CutTop0H3NegChart_ok : CutTop0H3NegChartTree.geometryOK CutTop0H3NegPowerCache CutTop0H3NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop0H3NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop0H3NegChartPart1_ok) (RatioChart.geometryCut_ok (CutTop0H3NegChartPart2_ok) (CutTop0H3NegChartPart3_ok))) (CutTop0H3NegChartPart4_ok))) (CutTop0H3NegChartPart5_ok)

end HlawkaSchatten.BelowExponent.G3P
