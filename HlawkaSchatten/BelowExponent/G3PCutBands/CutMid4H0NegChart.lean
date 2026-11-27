/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegChartPart7

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H0NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H0NegChartBox : Box := ⟨![0, 13/100, 0, -1], ![9/68, 3/20, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutMid4H0NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutMid4H0NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid4H0NegChartPart1Tree) (.cut 2 (5/16) (.cut 1 (7/50) (CutMid4H0NegChartPart2Tree) (.cut 0 (9/136) (CutMid4H0NegChartPart3Tree) (CutMid4H0NegChartPart4Tree))) (CutMid4H0NegChartPart5Tree))) (CutMid4H0NegChartPart6Tree))) (CutMid4H0NegChartPart7Tree)

set_option maxRecDepth 16000 in
theorem CutMid4H0NegChart_ok : CutMid4H0NegChartTree.geometryOK CutMid4H0NegPowerCache CutMid4H0NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid4H0NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid4H0NegChartPart1_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid4H0NegChartPart2_ok) (RatioChart.geometryCut_ok (CutMid4H0NegChartPart3_ok) (CutMid4H0NegChartPart4_ok))) (CutMid4H0NegChartPart5_ok))) (CutMid4H0NegChartPart6_ok))) (CutMid4H0NegChartPart7_ok)

end HlawkaSchatten.BelowExponent.G3P
