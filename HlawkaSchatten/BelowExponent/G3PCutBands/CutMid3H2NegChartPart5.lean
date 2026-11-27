/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2NegChartPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H2NegChartPart5Box : Box := ((((⟨![9/34, 11/100, 0, -1], ![27/68, 13/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid3H2NegChartPart5Tree : RatioChart :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨95281442640, 103236350716, (.direct 28300849942 32360437260), 91625974997, 274877906944, 469664387077/274877906944, .leaf (.secant 815046710230 342509872 34922204517 10180561190)⟩)
      (.cut 0 (45/136)
        (.cut 3 (-1/16)
          (.row ⟨95281442640, 103236350716, (.direct 8470703746 11065777119), 91625974997, 274877906944, 227287001233/137438953472, .leaf (.secant 735220963489 12143197460 34177188290 3393509060)⟩)
          (.row ⟨95281442640, 103236350716, (.direct 2220846419 4036762942), 91625974997, 274877906944, 30078370751/17179869184, .leaf (.secant 696457050405 21819544075 47625610649 0)⟩))
        (.cut 3 (-1/16)
          (.row ⟨95281442640, 103236350716, (.direct 8053620733 11158401966), 91625974997, 274877906944, 449393227521/274877906944, .leaf (.secant 694201015171 22451666156 48467052168 3393509060)⟩)
          (.row ⟨95281442640, 103236350716, (.direct 1952023257 4105270723), 91625974997, 274877906944, 471177965783/274877906944, .leaf (.secant 656263828223 34176967371 63582830215 0)⟩))))
    (.cut 3 (1/8)
      (.row ⟨95281442640, 103236350716, (.direct 377904493 260976857), 91625974997, 274877906944, 59125459219/34359738368, .leaf (.midpoint ⟨658473599885, 33437899883, 84214525667, 636287527261, 126320955114, 345448164409⟩)⟩)
      (.row ⟨95281442640, 103236350716, (.direct 4931790683 2332827362), 91625974997, 274877906944, 466298264287/274877906944, .leaf (.midpoint ⟨584894888331, 61726448972, 124257193506, 482827951909, 158392397362, 328044729802⟩)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H2NegChartPart5_ok : CutMid3H2NegChartPart5Tree.geometryOK CutMid3H2NegPowerCache CutMid3H2NegChartPart5Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
