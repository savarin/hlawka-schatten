/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H1NegChartPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H1NegChartPart5Box : Box := ((((⟨![9/68, 11/100, 0, -1], ![9/34, 13/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid3H1NegChartPart5Tree : RatioChart :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨95281442640, 103236350716, (.direct 29422139397 32122541870), 91625974997, 274877906944, 454207090251/274877906944, .leaf (.secant 902832344944 9247859247 12143314914 10180561190)⟩)
      (.cut 0 (27/136)
        (.row ⟨95281442640, 103236350716, (.direct 9317778972 10883524388), 91625974997, 274877906944, 258308744047/137438953472, .leaf (.secant 819836417934 114169576 21194278130 0)⟩)
        (.row ⟨95281442640, 103236350716, (.direct 8892167993 10974156044), 91625974997, 274877906944, 512678298283/274877906944, .leaf (.secant 777103573830 4390537685 33438118291 0)⟩)))
    (.cut 3 (1/8)
      (.row ⟨95281442640, 103236350716, (.direct 124421370 209431193), 91625974997, 274877906944, 256225380187/137438953472, .leaf (.midpoint ⟨739832218923, 11145929393, 56143020797, 848383425373, 84213688747, 363221546020⟩)⟩)
      (.row ⟨95281442640, 103236350716, (.direct 4130236857 2461969325), 91625974997, 274877906944, 497648451071/274877906944, .leaf (.midpoint ⟨662901361859, 31977740914, 104425363607, 546224978863, 124256364695, 346452473114⟩)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H1NegChartPart5_ok : CutMid3H1NegChartPart5Tree.ok CutMid3H1NegChartPart5Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
