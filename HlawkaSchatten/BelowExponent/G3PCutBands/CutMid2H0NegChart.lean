/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegChartPart7

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0NegChartBox : Box := ⟨![0, 9/100, 0, -1], ![9/68, 11/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutMid2H0NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutMid2H0NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid2H0NegChartPart1Tree) (.cut 2 (5/16) (.cut 2 (7/32) (.cut 1 (1/10) (CutMid2H0NegChartPart2Tree) (CutMid2H0NegChartPart3Tree)) (CutMid2H0NegChartPart4Tree)) (CutMid2H0NegChartPart5Tree))) (CutMid2H0NegChartPart6Tree))) (CutMid2H0NegChartPart7Tree)

set_option maxRecDepth 16000 in
theorem CutMid2H0NegChart_ok : CutMid2H0NegChartTree.geometryOK CutMid2H0NegPowerCache CutMid2H0NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid2H0NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid2H0NegChartPart1_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid2H0NegChartPart2_ok) (CutMid2H0NegChartPart3_ok)) (CutMid2H0NegChartPart4_ok)) (CutMid2H0NegChartPart5_ok))) (CutMid2H0NegChartPart6_ok))) (CutMid2H0NegChartPart7_ok)

end HlawkaSchatten.BelowExponent.G3P
