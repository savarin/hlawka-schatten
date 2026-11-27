/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegChartPart5

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1NegChartBox : Box := ⟨![9/68, 9/100, 0, -1], ![9/34, 11/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutMid2H1NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutMid2H1NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutMid2H1NegChartPart1Tree) (.cut 2 (5/16) (CutMid2H1NegChartPart2Tree) (CutMid2H1NegChartPart3Tree))) (CutMid2H1NegChartPart4Tree))) (CutMid2H1NegChartPart5Tree)

set_option maxRecDepth 16000 in
theorem CutMid2H1NegChart_ok : CutMid2H1NegChartTree.geometryOK CutMid2H1NegPowerCache CutMid2H1NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid2H1NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutMid2H1NegChartPart1_ok) (RatioChart.geometryCut_ok (CutMid2H1NegChartPart2_ok) (CutMid2H1NegChartPart3_ok))) (CutMid2H1NegChartPart4_ok))) (CutMid2H1NegChartPart5_ok)

end HlawkaSchatten.BelowExponent.G3P
