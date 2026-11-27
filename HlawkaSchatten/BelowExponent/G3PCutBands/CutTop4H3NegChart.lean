/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegChartPart26

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H3NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H3NegChartBox : Box := ⟨![27/136, 19/100, 0, -1], ![9/34, 1/5, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop4H3NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop4H3NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H3NegChartPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop4H3NegChartPart2Tree) (.cut 3 (-1/16) (CutTop4H3NegChartPart3Tree) (.cut 3 (-1/32) (CutTop4H3NegChartPart4Tree) (CutTop4H3NegChartPart5Tree)))) (CutTop4H3NegChartPart6Tree)) (.cut 3 (0) (.cut 3 (-1/8) (CutTop4H3NegChartPart7Tree) (.cut 3 (-1/16) (.cut 0 (63/272) (CutTop4H3NegChartPart8Tree) (CutTop4H3NegChartPart9Tree)) (.cut 3 (-1/32) (.cut 0 (63/272) (CutTop4H3NegChartPart10Tree) (.cut 2 (13/32) (CutTop4H3NegChartPart11Tree) (CutTop4H3NegChartPart12Tree))) (.cut 0 (63/272) (.cut 3 (-1/64) (CutTop4H3NegChartPart13Tree) (CutTop4H3NegChartPart14Tree)) (.cut 3 (-1/64) (CutTop4H3NegChartPart15Tree) (CutTop4H3NegChartPart16Tree)))))) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 0 (63/272) (.cut 2 (13/32) (.cut 3 (1/32) (CutTop4H3NegChartPart17Tree) (CutTop4H3NegChartPart18Tree)) (CutTop4H3NegChartPart19Tree)) (.cut 2 (13/32) (CutTop4H3NegChartPart20Tree) (CutTop4H3NegChartPart21Tree))) (.cut 2 (13/32) (CutTop4H3NegChartPart22Tree) (CutTop4H3NegChartPart23Tree))) (CutTop4H3NegChartPart24Tree))))) (CutTop4H3NegChartPart25Tree))) (CutTop4H3NegChartPart26Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H3NegChart_ok : CutTop4H3NegChartTree.ok CutTop4H3NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H3NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H3NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H3NegChartPart2_ok) (RatioChart.cut_ok (CutTop4H3NegChartPart3_ok) (RatioChart.cut_ok (CutTop4H3NegChartPart4_ok) (CutTop4H3NegChartPart5_ok)))) (CutTop4H3NegChartPart6_ok)) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H3NegChartPart7_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H3NegChartPart8_ok) (CutTop4H3NegChartPart9_ok)) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H3NegChartPart10_ok) (RatioChart.cut_ok (CutTop4H3NegChartPart11_ok) (CutTop4H3NegChartPart12_ok))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H3NegChartPart13_ok) (CutTop4H3NegChartPart14_ok)) (RatioChart.cut_ok (CutTop4H3NegChartPart15_ok) (CutTop4H3NegChartPart16_ok)))))) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H3NegChartPart17_ok) (CutTop4H3NegChartPart18_ok)) (CutTop4H3NegChartPart19_ok)) (RatioChart.cut_ok (CutTop4H3NegChartPart20_ok) (CutTop4H3NegChartPart21_ok))) (RatioChart.cut_ok (CutTop4H3NegChartPart22_ok) (CutTop4H3NegChartPart23_ok))) (CutTop4H3NegChartPart24_ok))))) (CutTop4H3NegChartPart25_ok))) (CutTop4H3NegChartPart26_ok)

end HlawkaSchatten.BelowExponent.G3P
