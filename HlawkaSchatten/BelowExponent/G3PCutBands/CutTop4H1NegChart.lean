/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart28
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart29
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegChartPart30

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H1NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H1NegChartBox : Box := ⟨![9/136, 19/100, 0, -1], ![9/68, 1/5, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop4H1NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop4H1NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H1NegChartPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (CutTop4H1NegChartPart2Tree) (.cut 0 (27/272) (.cut 3 (1/8) (CutTop4H1NegChartPart3Tree) (CutTop4H1NegChartPart4Tree)) (CutTop4H1NegChartPart5Tree))) (.cut 3 (0) (.cut 3 (-1/8) (CutTop4H1NegChartPart6Tree) (.cut 3 (-1/16) (CutTop4H1NegChartPart7Tree) (.cut 3 (-1/32) (CutTop4H1NegChartPart8Tree) (.cut 0 (27/272) (CutTop4H1NegChartPart9Tree) (CutTop4H1NegChartPart10Tree))))) (.cut 3 (1/8) (.cut 3 (1/16) (.cut 3 (1/32) (CutTop4H1NegChartPart11Tree) (CutTop4H1NegChartPart12Tree)) (.cut 2 (13/32) (.cut 0 (27/272) (CutTop4H1NegChartPart13Tree) (.cut 3 (3/32) (CutTop4H1NegChartPart14Tree) (CutTop4H1NegChartPart15Tree))) (CutTop4H1NegChartPart16Tree))) (.cut 3 (3/16) (.cut 2 (13/32) (.cut 0 (27/272) (.cut 1 (39/200) (CutTop4H1NegChartPart17Tree) (CutTop4H1NegChartPart18Tree)) (CutTop4H1NegChartPart19Tree)) (CutTop4H1NegChartPart20Tree)) (.cut 2 (13/32) (CutTop4H1NegChartPart21Tree) (CutTop4H1NegChartPart22Tree))))))) (CutTop4H1NegChartPart23Tree))) (.cut 3 (3/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H1NegChartPart24Tree) (.cut 3 (1/2) (.cut 2 (5/16) (CutTop4H1NegChartPart25Tree) (.cut 3 (3/8) (CutTop4H1NegChartPart26Tree) (CutTop4H1NegChartPart27Tree))) (CutTop4H1NegChartPart28Tree))) (CutTop4H1NegChartPart29Tree)) (CutTop4H1NegChartPart30Tree))

set_option maxRecDepth 16000 in
theorem CutTop4H1NegChart_ok : CutTop4H1NegChartTree.geometryOK CutTop4H1NegPowerCache CutTop4H1NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H1NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H1NegChartPart1_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H1NegChartPart2_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H1NegChartPart3_ok) (CutTop4H1NegChartPart4_ok)) (CutTop4H1NegChartPart5_ok))) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H1NegChartPart6_ok) (RatioChart.geometryCut_ok (CutTop4H1NegChartPart7_ok) (RatioChart.geometryCut_ok (CutTop4H1NegChartPart8_ok) (RatioChart.geometryCut_ok (CutTop4H1NegChartPart9_ok) (CutTop4H1NegChartPart10_ok))))) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H1NegChartPart11_ok) (CutTop4H1NegChartPart12_ok)) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H1NegChartPart13_ok) (RatioChart.geometryCut_ok (CutTop4H1NegChartPart14_ok) (CutTop4H1NegChartPart15_ok))) (CutTop4H1NegChartPart16_ok))) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H1NegChartPart17_ok) (CutTop4H1NegChartPart18_ok)) (CutTop4H1NegChartPart19_ok)) (CutTop4H1NegChartPart20_ok)) (RatioChart.geometryCut_ok (CutTop4H1NegChartPart21_ok) (CutTop4H1NegChartPart22_ok))))))) (CutTop4H1NegChartPart23_ok))) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H1NegChartPart24_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H1NegChartPart25_ok) (RatioChart.geometryCut_ok (CutTop4H1NegChartPart26_ok) (CutTop4H1NegChartPart27_ok))) (CutTop4H1NegChartPart28_ok))) (CutTop4H1NegChartPart29_ok)) (CutTop4H1NegChartPart30_ok))

end HlawkaSchatten.BelowExponent.G3P
