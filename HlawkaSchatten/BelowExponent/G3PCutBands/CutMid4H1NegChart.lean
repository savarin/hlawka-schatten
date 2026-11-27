/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegChartPart9

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H1NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H1NegChartBox : Box := ⟨![9/68, 13/100, 0, -1], ![9/34, 3/20, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutMid4H1NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutMid4H1NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid4H1NegChartPart1Tree) (.cut 2 (5/16) (.cut 0 (27/136) (.cut 1 (7/50) (CutMid4H1NegChartPart2Tree) (CutMid4H1NegChartPart3Tree)) (.cut 1 (7/50) (CutMid4H1NegChartPart4Tree) (CutMid4H1NegChartPart5Tree))) (.cut 3 (0) (CutMid4H1NegChartPart6Tree) (CutMid4H1NegChartPart7Tree)))) (CutMid4H1NegChartPart8Tree))) (CutMid4H1NegChartPart9Tree)

set_option maxRecDepth 16000 in
theorem CutMid4H1NegChart_ok : CutMid4H1NegChartTree.geometryOK CutMid4H1NegPowerCache CutMid4H1NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid4H1NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid4H1NegChartPart1_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid4H1NegChartPart2_ok) (CutMid4H1NegChartPart3_ok)) (RatioChart.geometryCut_ok (CutMid4H1NegChartPart4_ok) (CutMid4H1NegChartPart5_ok))) (RatioChart.geometryCut_ok (CutMid4H1NegChartPart6_ok) (CutMid4H1NegChartPart7_ok)))) (CutMid4H1NegChartPart8_ok))) (CutMid4H1NegChartPart9_ok)

end HlawkaSchatten.BelowExponent.G3P
