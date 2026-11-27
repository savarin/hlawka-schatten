/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegChartPart28

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H5NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H5NegChartBox : Box := ⟨![45/136, 19/100, 0, -1], ![27/68, 1/5, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop4H5NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop4H5NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H5NegChartPart1Tree) (.cut 3 (0) (.cut 3 (-1/8) (.cut 2 (5/16) (CutTop4H5NegChartPart2Tree) (CutTop4H5NegChartPart3Tree)) (.cut 3 (-1/16) (.cut 2 (5/16) (CutTop4H5NegChartPart4Tree) (.cut 0 (99/272) (.cut 3 (-3/32) (CutTop4H5NegChartPart5Tree) (.cut 2 (13/32) (CutTop4H5NegChartPart6Tree) (CutTop4H5NegChartPart7Tree))) (.cut 3 (-3/32) (CutTop4H5NegChartPart8Tree) (.cut 2 (13/32) (CutTop4H5NegChartPart9Tree) (CutTop4H5NegChartPart10Tree))))) (.cut 2 (5/16) (CutTop4H5NegChartPart11Tree) (.cut 3 (-1/32) (.cut 0 (99/272) (.cut 3 (-3/64) (CutTop4H5NegChartPart12Tree) (CutTop4H5NegChartPart13Tree)) (.cut 3 (-3/64) (CutTop4H5NegChartPart14Tree) (CutTop4H5NegChartPart15Tree))) (.cut 0 (99/272) (.cut 3 (-1/64) (CutTop4H5NegChartPart16Tree) (CutTop4H5NegChartPart17Tree)) (CutTop4H5NegChartPart18Tree)))))) (.cut 3 (1/8) (.cut 2 (5/16) (CutTop4H5NegChartPart19Tree) (.cut 3 (1/16) (.cut 0 (99/272) (CutTop4H5NegChartPart20Tree) (CutTop4H5NegChartPart21Tree)) (CutTop4H5NegChartPart22Tree))) (CutTop4H5NegChartPart23Tree)))) (.cut 2 (3/4) (.cut 3 (0) (.cut 3 (-1/8) (CutTop4H5NegChartPart24Tree) (CutTop4H5NegChartPart25Tree)) (CutTop4H5NegChartPart26Tree)) (CutTop4H5NegChartPart27Tree)))) (CutTop4H5NegChartPart28Tree)

set_option maxRecDepth 16000 in
theorem CutTop4H5NegChart_ok : CutTop4H5NegChartTree.ok CutTop4H5NegChartBox false = true :=
  RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H5NegChartPart0_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H5NegChartPart1_ok) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H5NegChartPart2_ok) (CutTop4H5NegChartPart3_ok)) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H5NegChartPart4_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H5NegChartPart5_ok) (RatioChart.cut_ok (CutTop4H5NegChartPart6_ok) (CutTop4H5NegChartPart7_ok))) (RatioChart.cut_ok (CutTop4H5NegChartPart8_ok) (RatioChart.cut_ok (CutTop4H5NegChartPart9_ok) (CutTop4H5NegChartPart10_ok))))) (RatioChart.cut_ok (CutTop4H5NegChartPart11_ok) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H5NegChartPart12_ok) (CutTop4H5NegChartPart13_ok)) (RatioChart.cut_ok (CutTop4H5NegChartPart14_ok) (CutTop4H5NegChartPart15_ok))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H5NegChartPart16_ok) (CutTop4H5NegChartPart17_ok)) (CutTop4H5NegChartPart18_ok)))))) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H5NegChartPart19_ok) (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H5NegChartPart20_ok) (CutTop4H5NegChartPart21_ok)) (CutTop4H5NegChartPart22_ok))) (CutTop4H5NegChartPart23_ok)))) (RatioChart.cut_ok (RatioChart.cut_ok (RatioChart.cut_ok (CutTop4H5NegChartPart24_ok) (CutTop4H5NegChartPart25_ok)) (CutTop4H5NegChartPart26_ok)) (CutTop4H5NegChartPart27_ok)))) (CutTop4H5NegChartPart28_ok)

end HlawkaSchatten.BelowExponent.G3P
