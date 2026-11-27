/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegChartPart19

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7NegChartBox : Box := ⟨![63/136, 19/100, 0, -1], ![9/17, 1/5, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop4H7NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop4H7NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H7NegChartPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (.cut 3 (-3/16) (CutTop4H7NegChartPart2Tree) (.cut 2 (5/16) (CutTop4H7NegChartPart3Tree) (.cut 0 (135/272) (CutTop4H7NegChartPart4Tree) (CutTop4H7NegChartPart5Tree)))) (.cut 3 (-1/16) (.cut 2 (5/16) (CutTop4H7NegChartPart6Tree) (.cut 3 (-3/32) (.cut 0 (135/272) (CutTop4H7NegChartPart7Tree) (CutTop4H7NegChartPart8Tree)) (.cut 0 (135/272) (CutTop4H7NegChartPart9Tree) (CutTop4H7NegChartPart10Tree)))) (.cut 3 (-1/32) (.cut 2 (5/16) (CutTop4H7NegChartPart11Tree) (CutTop4H7NegChartPart12Tree)) (CutTop4H7NegChartPart13Tree)))) (CutTop4H7NegChartPart14Tree))) (.cut 3 (0) (.cut 3 (-1/8) (CutTop4H7NegChartPart15Tree) (.cut 3 (-1/16) (CutTop4H7NegChartPart16Tree) (CutTop4H7NegChartPart17Tree))) (CutTop4H7NegChartPart18Tree)))) (CutTop4H7NegChartPart19Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H7NegChart_ok : CutTop4H7NegChartTree.ok CutTop4H7NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H7NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H7NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H7NegChartPart2_ok) (RatioChart.cut_ok (CutTop4H7NegChartPart3_ok) (RatioChart.cut_ok (CutTop4H7NegChartPart4_ok) (CutTop4H7NegChartPart5_ok)))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H7NegChartPart6_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H7NegChartPart7_ok) (CutTop4H7NegChartPart8_ok)) (RatioChart.cut_ok (CutTop4H7NegChartPart9_ok) (CutTop4H7NegChartPart10_ok)))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H7NegChartPart11_ok) (CutTop4H7NegChartPart12_ok)) (CutTop4H7NegChartPart13_ok)))) (CutTop4H7NegChartPart14_ok))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H7NegChartPart15_ok) (RatioChart.cut_ok (CutTop4H7NegChartPart16_ok) (CutTop4H7NegChartPart17_ok))) (CutTop4H7NegChartPart18_ok)))) (CutTop4H7NegChartPart19_ok)

end HlawkaSchatten.BelowExponent.G3P
