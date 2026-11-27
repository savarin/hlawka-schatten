/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegChartPart12

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H5NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H5NegChartBox : Box := ⟨![45/136, 9/50, 0, -1], ![27/68, 19/100, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop3H5NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop3H5NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop3H5NegChartPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (CutTop3H5NegChartPart2Tree) (.cut 3 (-1/16) (.cut 2 (5/16) (CutTop3H5NegChartPart3Tree) (.cut 0 (99/272) (CutTop3H5NegChartPart4Tree) (CutTop3H5NegChartPart5Tree))) (.cut 2 (5/16) (CutTop3H5NegChartPart6Tree) (.cut 3 (-1/32) (.cut 0 (99/272) (CutTop3H5NegChartPart7Tree) (CutTop3H5NegChartPart8Tree)) (CutTop3H5NegChartPart9Tree))))) (CutTop3H5NegChartPart10Tree))) (CutTop3H5NegChartPart11Tree))) (CutTop3H5NegChartPart12Tree)

set_option maxRecDepth 16000 in
theorem CutTop3H5NegChart_ok : CutTop3H5NegChartTree.geometryOK CutTop3H5NegPowerCache CutTop3H5NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop3H5NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop3H5NegChartPart1_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop3H5NegChartPart2_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop3H5NegChartPart3_ok) (RatioChart.geometryCut_ok (CutTop3H5NegChartPart4_ok) (CutTop3H5NegChartPart5_ok))) (RatioChart.geometryCut_ok (CutTop3H5NegChartPart6_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop3H5NegChartPart7_ok) (CutTop3H5NegChartPart8_ok)) (CutTop3H5NegChartPart9_ok))))) (CutTop3H5NegChartPart10_ok))) (CutTop3H5NegChartPart11_ok))) (CutTop3H5NegChartPart12_ok)

end HlawkaSchatten.BelowExponent.G3P
