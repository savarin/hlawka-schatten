/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegChartPart6

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H2NegChartBox : Box := ⟨![9/34, 11/100, 0, -1], ![27/68, 13/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutMid3H2NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutMid3H2NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid3H2NegChartPart1Tree) (.cut 2 (5/16) (.cut 1 (3/25) (CutMid3H2NegChartPart2Tree) (CutMid3H2NegChartPart3Tree)) (CutMid3H2NegChartPart4Tree))) (CutMid3H2NegChartPart5Tree))) (CutMid3H2NegChartPart6Tree)

set_option maxRecDepth 16000 in
theorem CutMid3H2NegChart_ok : CutMid3H2NegChartTree.geometryOK CutMid3H2NegPowerCache CutMid3H2NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid3H2NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid3H2NegChartPart1_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid3H2NegChartPart2_ok) (CutMid3H2NegChartPart3_ok)) (CutMid3H2NegChartPart4_ok))) (CutMid3H2NegChartPart5_ok))) (CutMid3H2NegChartPart6_ok)

end HlawkaSchatten.BelowExponent.G3P
