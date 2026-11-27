/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegChartPart4

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H2NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H2NegChartBox : Box := ⟨![9/34, 7/100, 0, -1], ![27/68, 9/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutMid1H2NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutMid1H2NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid1H2NegChartPart1Tree) (CutMid1H2NegChartPart2Tree)) (CutMid1H2NegChartPart3Tree))) (CutMid1H2NegChartPart4Tree)

set_option maxRecDepth 16000 in
theorem CutMid1H2NegChart_ok : CutMid1H2NegChartTree.geometryOK CutMid1H2NegPowerCache CutMid1H2NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid1H2NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid1H2NegChartPart1_ok) (CutMid1H2NegChartPart2_ok)) (CutMid1H2NegChartPart3_ok))) (CutMid1H2NegChartPart4_ok)

end HlawkaSchatten.BelowExponent.G3P
