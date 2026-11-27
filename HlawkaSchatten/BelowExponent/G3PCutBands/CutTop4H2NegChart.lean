/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegChartPart27

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegChartBox : Box := ⟨![9/68, 19/100, 0, -1], ![27/136, 1/5, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop4H2NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop4H2NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H2NegChartPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (.cut 3 (-1/8) (CutTop4H2NegChartPart2Tree) (.cut 3 (-1/16) (CutTop4H2NegChartPart3Tree) (.cut 3 (-1/32) (CutTop4H2NegChartPart4Tree) (CutTop4H2NegChartPart5Tree)))) (.cut 3 (1/8) (.cut 3 (1/16) (CutTop4H2NegChartPart6Tree) (CutTop4H2NegChartPart7Tree)) (CutTop4H2NegChartPart8Tree))) (.cut 3 (0) (.cut 3 (-1/8) (CutTop4H2NegChartPart9Tree) (.cut 3 (-1/16) (CutTop4H2NegChartPart10Tree) (.cut 3 (-1/32) (.cut 0 (45/272) (CutTop4H2NegChartPart11Tree) (CutTop4H2NegChartPart12Tree)) (.cut 0 (45/272) (CutTop4H2NegChartPart13Tree) (.cut 3 (-1/64) (CutTop4H2NegChartPart14Tree) (CutTop4H2NegChartPart15Tree)))))) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 3 (1/32) (.cut 0 (45/272) (CutTop4H2NegChartPart16Tree) (CutTop4H2NegChartPart17Tree)) (.cut 2 (13/32) (CutTop4H2NegChartPart18Tree) (CutTop4H2NegChartPart19Tree))) (.cut 2 (13/32) (.cut 0 (45/272) (CutTop4H2NegChartPart20Tree) (CutTop4H2NegChartPart21Tree)) (CutTop4H2NegChartPart22Tree))) (.cut 2 (13/32) (.cut 0 (45/272) (CutTop4H2NegChartPart23Tree) (CutTop4H2NegChartPart24Tree)) (CutTop4H2NegChartPart25Tree)))))) (CutTop4H2NegChartPart26Tree))) (CutTop4H2NegChartPart27Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H2NegChart_ok : CutTop4H2NegChartTree.ok CutTop4H2NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H2NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H2NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H2NegChartPart2_ok) (RatioChart.cut_ok (CutTop4H2NegChartPart3_ok) (RatioChart.cut_ok (CutTop4H2NegChartPart4_ok) (CutTop4H2NegChartPart5_ok)))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H2NegChartPart6_ok) (CutTop4H2NegChartPart7_ok)) (CutTop4H2NegChartPart8_ok))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H2NegChartPart9_ok) (RatioChart.cut_ok (CutTop4H2NegChartPart10_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H2NegChartPart11_ok) (CutTop4H2NegChartPart12_ok)) (RatioChart.cut_ok (CutTop4H2NegChartPart13_ok) (RatioChart.cut_ok (CutTop4H2NegChartPart14_ok) (CutTop4H2NegChartPart15_ok)))))) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H2NegChartPart16_ok) (CutTop4H2NegChartPart17_ok)) (RatioChart.cut_ok (CutTop4H2NegChartPart18_ok) (CutTop4H2NegChartPart19_ok))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H2NegChartPart20_ok) (CutTop4H2NegChartPart21_ok)) (CutTop4H2NegChartPart22_ok))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H2NegChartPart23_ok) (CutTop4H2NegChartPart24_ok)) (CutTop4H2NegChartPart25_ok)))))) (CutTop4H2NegChartPart26_ok))) (CutTop4H2NegChartPart27_ok)

end HlawkaSchatten.BelowExponent.G3P
