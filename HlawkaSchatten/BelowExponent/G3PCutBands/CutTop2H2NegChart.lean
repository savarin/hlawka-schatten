/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegChartPart7

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H2NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H2NegChartBox : Box := ⟨![9/68, 17/100, 0, -1], ![27/136, 9/50, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop2H2NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop2H2NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop2H2NegChartPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (CutTop2H2NegChartPart2Tree) (CutTop2H2NegChartPart3Tree)) (.cut 3 (0) (CutTop2H2NegChartPart4Tree) (CutTop2H2NegChartPart5Tree)))) (CutTop2H2NegChartPart6Tree))) (CutTop2H2NegChartPart7Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H2NegChart_ok : CutTop2H2NegChartTree.geometryOK CutTop2H2NegPowerCache CutTop2H2NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop2H2NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop2H2NegChartPart1_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop2H2NegChartPart2_ok) (CutTop2H2NegChartPart3_ok)) (RatioChart.geometryCut_ok (CutTop2H2NegChartPart4_ok) (CutTop2H2NegChartPart5_ok)))) (CutTop2H2NegChartPart6_ok))) (CutTop2H2NegChartPart7_ok)

end HlawkaSchatten.BelowExponent.G3P
