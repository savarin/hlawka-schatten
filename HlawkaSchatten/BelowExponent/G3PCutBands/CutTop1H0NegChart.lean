/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H0NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H0NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H0NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H0NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H0NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H0NegChartPart5

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H0NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H0NegChartBox : Box := ⟨![0, 4/25, 0, -1], ![9/136, 17/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop1H0NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop1H0NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop1H0NegChartPart1Tree) (.cut 2 (5/16) (CutTop1H0NegChartPart2Tree) (CutTop1H0NegChartPart3Tree))) (CutTop1H0NegChartPart4Tree))) (CutTop1H0NegChartPart5Tree)

set_option maxRecDepth 16000 in
theorem CutTop1H0NegChart_ok : CutTop1H0NegChartTree.geometryOK CutTop1H0NegPowerCache CutTop1H0NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop1H0NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop1H0NegChartPart1_ok) (RatioChart.geometryCut_ok (CutTop1H0NegChartPart2_ok) (CutTop1H0NegChartPart3_ok))) (CutTop1H0NegChartPart4_ok))) (CutTop1H0NegChartPart5_ok)

end HlawkaSchatten.BelowExponent.G3P
