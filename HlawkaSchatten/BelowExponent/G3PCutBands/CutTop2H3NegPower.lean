/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H3NegPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H3NegPowerCache : PowerCache :=
  ⟨[(5/16, 43500686443), (13/32, 65931360876), (7/32, 24716235638), (1/2, 91625974997), (1/8, 10180665226), (3/4, 174227471798), (11/64, 16864782083), (19/128, 13368036905), (0, 0), (17/64, 33622326476), (1, 274877906944), (1/16, 3393555298), (23/64, 54287507865), (25/128, 20652546629)], [((9/50, 120689819475/274877906944), (12, 25)), ((117423580139/274877906944, 17/100), (25, 12)), ((59534416705/137438953472, 7/40), (25, 12)), ((7/40, 119068833411/274877906944), (12, 25)), ((71/400, 29970573639/68719476736), (12, 25)), ((119882294555/274877906944, 71/400), (25, 12)), ((69/400, 59124653325/137438953472), (12, 25)), ((118249306649/274877906944, 69/400), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutTop2H3NegPowerCache_valid : CutTop2H3NegPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
