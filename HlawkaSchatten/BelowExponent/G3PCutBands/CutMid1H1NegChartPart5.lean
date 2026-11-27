/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H1NegChartPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H1NegChartPart5Box : Box := ((((((⟨![9/68, 7/100, 0, -1], ![9/34, 9/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 2 (5/16)

set_option maxRecDepth 16000 in
def CutMid1H1NegChartPart5Tree : RatioChart :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨76698504228, 86531900009, (.direct 9641145629 11065134120), 43500686443, 91625974997, 454207090251/274877906944, .leaf (.secant 902832344944 9247859247 12143314914 10180561190)⟩)
      (.cut 0 (27/136)
        (.row ⟨76698504228, 86531900009, (.direct 3012672150 3770122321), 43500686443, 91625974997, 258308744047/137438953472, .leaf (.secant 819836417934 114169576 21194278130 0)⟩)
        (.row ⟨76698504228, 86531900009, (.direct 2827273363 3831901432), 43500686443, 91625974997, 512678298283/274877906944, .leaf (.secant 777103573830 4390537685 33438118291 0)⟩)))
    (.cut 3 (1/8)
      (.row ⟨76698504228, 86531900009, (.direct 58525842 123075976), 43500686443, 91625974997, 256225380187/137438953472, .leaf (.midpoint ⟨739832218923, 11145929393, 56143020797, 848383425373, 84213688747, 363221546020⟩)⟩)
      (.row ⟨76698504228, 86531900009, (.direct 1950833535 1119826190), 43500686443, 91625974997, 497648451071/274877906944, .leaf (.midpoint ⟨662901361859, 31977740914, 104425363607, 546224978863, 124256364695, 346452473114⟩)⟩))

set_option maxRecDepth 16000 in
theorem CutMid1H1NegChartPart5_ok : CutMid1H1NegChartPart5Tree.geometryOK CutMid1H1NegPowerCache CutMid1H1NegChartPart5Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
