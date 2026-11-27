/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegChartPart24

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H6NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H6NegChartBox : Box := ⟨![27/68, 19/100, 0, -1], ![63/136, 1/5, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop4H6NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop4H6NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H6NegChartPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (.cut 3 (-3/16) (CutTop4H6NegChartPart2Tree) (.cut 2 (5/16) (CutTop4H6NegChartPart3Tree) (.cut 0 (117/272) (CutTop4H6NegChartPart4Tree) (CutTop4H6NegChartPart5Tree)))) (.cut 3 (-1/16) (.cut 2 (5/16) (CutTop4H6NegChartPart6Tree) (.cut 0 (117/272) (.cut 3 (-3/32) (CutTop4H6NegChartPart7Tree) (.cut 3 (-5/64) (CutTop4H6NegChartPart8Tree) (CutTop4H6NegChartPart9Tree))) (.cut 3 (-3/32) (CutTop4H6NegChartPart10Tree) (CutTop4H6NegChartPart11Tree)))) (.cut 2 (5/16) (CutTop4H6NegChartPart12Tree) (.cut 3 (-1/32) (.cut 0 (117/272) (CutTop4H6NegChartPart13Tree) (CutTop4H6NegChartPart14Tree)) (.cut 0 (117/272) (CutTop4H6NegChartPart15Tree) (CutTop4H6NegChartPart16Tree)))))) (.cut 3 (1/8) (CutTop4H6NegChartPart17Tree) (CutTop4H6NegChartPart18Tree)))) (.cut 2 (3/4) (.cut 3 (0) (.cut 3 (-1/8) (CutTop4H6NegChartPart19Tree) (.cut 3 (-1/16) (CutTop4H6NegChartPart20Tree) (CutTop4H6NegChartPart21Tree))) (CutTop4H6NegChartPart22Tree)) (CutTop4H6NegChartPart23Tree)))) (CutTop4H6NegChartPart24Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H6NegChart_ok : CutTop4H6NegChartTree.ok CutTop4H6NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H6NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H6NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H6NegChartPart2_ok) (RatioChart.cut_ok (CutTop4H6NegChartPart3_ok) (RatioChart.cut_ok (CutTop4H6NegChartPart4_ok) (CutTop4H6NegChartPart5_ok)))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H6NegChartPart6_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H6NegChartPart7_ok) (RatioChart.cut_ok (CutTop4H6NegChartPart8_ok) (CutTop4H6NegChartPart9_ok))) (RatioChart.cut_ok (CutTop4H6NegChartPart10_ok) (CutTop4H6NegChartPart11_ok)))) (RatioChart.cut_ok (CutTop4H6NegChartPart12_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H6NegChartPart13_ok) (CutTop4H6NegChartPart14_ok)) (RatioChart.cut_ok (CutTop4H6NegChartPart15_ok) (CutTop4H6NegChartPart16_ok)))))) (RatioChart.cut_ok (CutTop4H6NegChartPart17_ok) (CutTop4H6NegChartPart18_ok)))) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H6NegChartPart19_ok) (RatioChart.cut_ok (CutTop4H6NegChartPart20_ok) (CutTop4H6NegChartPart21_ok))) (CutTop4H6NegChartPart22_ok)) (CutTop4H6NegChartPart23_ok)))) (CutTop4H6NegChartPart24_ok)

end HlawkaSchatten.BelowExponent.G3P
