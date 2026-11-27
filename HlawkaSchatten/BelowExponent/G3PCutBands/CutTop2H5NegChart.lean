/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H5NegChartPart9

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H5NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H5NegChartBox : Box := ⟨![45/136, 17/100, 0, -1], ![27/68, 9/50, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop2H5NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop2H5NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop2H5NegChartPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (CutTop2H5NegChartPart2Tree) (.cut 3 (-1/16) (.cut 2 (5/16) (CutTop2H5NegChartPart3Tree) (CutTop2H5NegChartPart4Tree)) (.cut 2 (5/16) (CutTop2H5NegChartPart5Tree) (CutTop2H5NegChartPart6Tree)))) (CutTop2H5NegChartPart7Tree))) (CutTop2H5NegChartPart8Tree))) (CutTop2H5NegChartPart9Tree)

set_option maxRecDepth 16000 in
theorem CutTop2H5NegChart_ok : CutTop2H5NegChartTree.geometryOK CutTop2H5NegPowerCache CutTop2H5NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop2H5NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop2H5NegChartPart1_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop2H5NegChartPart2_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop2H5NegChartPart3_ok) (CutTop2H5NegChartPart4_ok)) (RatioChart.geometryCut_ok (CutTop2H5NegChartPart5_ok) (CutTop2H5NegChartPart6_ok)))) (CutTop2H5NegChartPart7_ok))) (CutTop2H5NegChartPart8_ok))) (CutTop2H5NegChartPart9_ok)

end HlawkaSchatten.BelowExponent.G3P
