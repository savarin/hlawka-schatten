/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart0
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart1
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart2
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart3
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart4
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart5
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart6
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart7
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart8
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart9
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart10
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart11
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart12
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart13
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart14
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart15
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart16
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart17
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart18
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart19
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart20
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart21
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart22
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart23
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart24
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart25
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart26
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart27
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart28
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart29
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart30
public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegChartPart31

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H0NegChart`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H0NegChartBox : Box := ⟨![0, 19/100, 0, -1], ![9/136, 1/5, 1, 1]⟩

set_option maxRecDepth 16000 in
def CutTop4H0NegChartTree : RatioChart :=
  .cut 3 (1/4) (.cut 3 (-1/4) (CutTop4H0NegChartPart0Tree) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H0NegChartPart1Tree) (.cut 2 (5/16) (.cut 3 (0) (CutTop4H0NegChartPart2Tree) (.cut 0 (9/272) (.cut 1 (39/200) (CutTop4H0NegChartPart3Tree) (CutTop4H0NegChartPart4Tree)) (.cut 1 (39/200) (CutTop4H0NegChartPart5Tree) (CutTop4H0NegChartPart6Tree)))) (.cut 3 (0) (CutTop4H0NegChartPart7Tree) (.cut 0 (9/272) (.cut 2 (13/32) (.cut 0 (9/544) (.cut 3 (1/8) (CutTop4H0NegChartPart8Tree) (.cut 3 (3/16) (CutTop4H0NegChartPart9Tree) (CutTop4H0NegChartPart10Tree))) (.cut 3 (1/8) (CutTop4H0NegChartPart11Tree) (.cut 3 (3/16) (CutTop4H0NegChartPart12Tree) (CutTop4H0NegChartPart13Tree)))) (CutTop4H0NegChartPart14Tree)) (.cut 3 (1/8) (.cut 3 (1/16) (CutTop4H0NegChartPart15Tree) (CutTop4H0NegChartPart16Tree)) (.cut 3 (3/16) (.cut 2 (13/32) (.cut 1 (39/200) (CutTop4H0NegChartPart17Tree) (CutTop4H0NegChartPart18Tree)) (CutTop4H0NegChartPart19Tree)) (.cut 2 (13/32) (CutTop4H0NegChartPart20Tree) (CutTop4H0NegChartPart21Tree)))))))) (CutTop4H0NegChartPart22Tree))) (.cut 3 (3/4) (.cut 2 (1/2) (.cut 2 (1/8) (CutTop4H0NegChartPart23Tree) (.cut 2 (5/16) (CutTop4H0NegChartPart24Tree) (.cut 3 (1/2) (.cut 3 (3/8) (.cut 2 (13/32) (.cut 0 (9/272) (CutTop4H0NegChartPart25Tree) (CutTop4H0NegChartPart26Tree)) (CutTop4H0NegChartPart27Tree)) (CutTop4H0NegChartPart28Tree)) (CutTop4H0NegChartPart29Tree)))) (CutTop4H0NegChartPart30Tree)) (CutTop4H0NegChartPart31Tree))

set_option maxRecDepth 16000 in
theorem CutTop4H0NegChart_ok : CutTop4H0NegChartTree.geometryOK CutTop4H0NegPowerCache CutTop4H0NegChartBox false = true :=
  RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H0NegChartPart0_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H0NegChartPart1_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H0NegChartPart2_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H0NegChartPart3_ok) (CutTop4H0NegChartPart4_ok)) (RatioChart.geometryCut_ok (CutTop4H0NegChartPart5_ok) (CutTop4H0NegChartPart6_ok)))) (RatioChart.geometryCut_ok (CutTop4H0NegChartPart7_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H0NegChartPart8_ok) (RatioChart.geometryCut_ok (CutTop4H0NegChartPart9_ok) (CutTop4H0NegChartPart10_ok))) (RatioChart.geometryCut_ok (CutTop4H0NegChartPart11_ok) (RatioChart.geometryCut_ok (CutTop4H0NegChartPart12_ok) (CutTop4H0NegChartPart13_ok)))) (CutTop4H0NegChartPart14_ok)) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H0NegChartPart15_ok) (CutTop4H0NegChartPart16_ok)) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H0NegChartPart17_ok) (CutTop4H0NegChartPart18_ok)) (CutTop4H0NegChartPart19_ok)) (RatioChart.geometryCut_ok (CutTop4H0NegChartPart20_ok) (CutTop4H0NegChartPart21_ok)))))))) (CutTop4H0NegChartPart22_ok))) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H0NegChartPart23_ok) (RatioChart.geometryCut_ok (CutTop4H0NegChartPart24_ok) (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (RatioChart.geometryCut_ok (CutTop4H0NegChartPart25_ok) (CutTop4H0NegChartPart26_ok)) (CutTop4H0NegChartPart27_ok)) (CutTop4H0NegChartPart28_ok)) (CutTop4H0NegChartPart29_ok)))) (CutTop4H0NegChartPart30_ok)) (CutTop4H0NegChartPart31_ok))

end HlawkaSchatten.BelowExponent.G3P
