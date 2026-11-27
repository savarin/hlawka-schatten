/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H4NegChartPart6

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H4NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H4NegChartBox : Box := ⟨![9/34, 4/25, 0, -1], ![45/136, 17/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop1H4NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop1H4NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop1H4NegChartPart1Tree) (.cut 2 (5/16) (CutTop1H4NegChartPart2Tree) (.cut 3 (0) (CutTop1H4NegChartPart3Tree) (CutTop1H4NegChartPart4Tree)))) (CutTop1H4NegChartPart5Tree))) (CutTop1H4NegChartPart6Tree)

set_option maxRecDepth 16000 in
theorem CutTop1H4NegChart_ok : CutTop1H4NegChartTree.geometryOK CutTop1H4NegPowerCache CutTop1H4NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop1H4NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop1H4NegChartPart1_ok) (RatioChart.geometryCut_ok (CutTop1H4NegChartPart2_ok) (RatioChart.geometryCut_ok (CutTop1H4NegChartPart3_ok) (CutTop1H4NegChartPart4_ok)))) (CutTop1H4NegChartPart5_ok))) (CutTop1H4NegChartPart6_ok)

end HlawkaSchatten.BelowExponent.G3P
