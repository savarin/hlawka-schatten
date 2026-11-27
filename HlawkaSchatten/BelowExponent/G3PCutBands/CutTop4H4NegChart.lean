/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H4NegChartPart25

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H4NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H4NegChartBox : Box := ⟨![9/34, 19/100, 0, -1], ![45/136, 1/5, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop4H4NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop4H4NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H4NegChartPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (CutTop4H4NegChartPart2Tree) (.cut 3 (-1/16) (.cut 2 (5/16) (CutTop4H4NegChartPart3Tree) (.cut 0 (81/272) (CutTop4H4NegChartPart4Tree) (.cut 3 (-3/32) (CutTop4H4NegChartPart5Tree) (CutTop4H4NegChartPart6Tree)))) (.cut 2 (5/16) (.cut 3 (-1/32) (CutTop4H4NegChartPart7Tree) (CutTop4H4NegChartPart8Tree)) (.cut 3 (-1/32) (.cut 0 (81/272) (.cut 2 (13/32) (CutTop4H4NegChartPart9Tree) (CutTop4H4NegChartPart10Tree)) (.cut 3 (-3/64) (CutTop4H4NegChartPart11Tree) (CutTop4H4NegChartPart12Tree))) (.cut 0 (81/272) (.cut 3 (-1/64) (CutTop4H4NegChartPart13Tree) (CutTop4H4NegChartPart14Tree)) (.cut 3 (-1/64) (CutTop4H4NegChartPart15Tree) (CutTop4H4NegChartPart16Tree))))))) (.cut 3 (1/8) (.cut 2 (5/16) (CutTop4H4NegChartPart17Tree) (.cut 3 (1/16) (.cut 0 (81/272) (.cut 2 (13/32) (CutTop4H4NegChartPart18Tree) (CutTop4H4NegChartPart19Tree)) (.cut 2 (13/32) (CutTop4H4NegChartPart20Tree) (CutTop4H4NegChartPart21Tree))) (CutTop4H4NegChartPart22Tree))) (CutTop4H4NegChartPart23Tree)))) (CutTop4H4NegChartPart24Tree))) (CutTop4H4NegChartPart25Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H4NegChart_ok : CutTop4H4NegChartTree.ok CutTop4H4NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H4NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H4NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H4NegChartPart2_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H4NegChartPart3_ok) (RatioChart.cut_ok (CutTop4H4NegChartPart4_ok) (RatioChart.cut_ok (CutTop4H4NegChartPart5_ok) (CutTop4H4NegChartPart6_ok)))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H4NegChartPart7_ok) (CutTop4H4NegChartPart8_ok)) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H4NegChartPart9_ok) (CutTop4H4NegChartPart10_ok)) (RatioChart.cut_ok (CutTop4H4NegChartPart11_ok) (CutTop4H4NegChartPart12_ok))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H4NegChartPart13_ok) (CutTop4H4NegChartPart14_ok)) (RatioChart.cut_ok (CutTop4H4NegChartPart15_ok) (CutTop4H4NegChartPart16_ok))))))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H4NegChartPart17_ok) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H4NegChartPart18_ok) (CutTop4H4NegChartPart19_ok)) (RatioChart.cut_ok (CutTop4H4NegChartPart20_ok) (CutTop4H4NegChartPart21_ok))) (CutTop4H4NegChartPart22_ok))) (CutTop4H4NegChartPart23_ok)))) (CutTop4H4NegChartPart24_ok))) (CutTop4H4NegChartPart25_ok)

end HlawkaSchatten.BelowExponent.G3P
