/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H7NegPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H7NegPowerCache : PowerCache :=
  ⟨[(5/16, 43500686443), (13/32, 65931360876), (1/2, 91625974997), (1/8, 10180665226), (7/32, 24716235638), (1, 274877906944), (3/4, 174227471798), (17/64, 33622326476), (11/64, 16864782083), (23/64, 54287507865), (0, 0), (19/128, 13368036905), (5/8, 130502050762)], [((9/50, 120689819475/274877906944), (12, 25)), ((117423580139/274877906944, 17/100), (25, 12)), ((59534416705/137438953472, 7/40), (25, 12)), ((7/40, 119068833411/274877906944), (12, 25))]⟩

set_option maxRecDepth 16000 in
theorem CutTop2H7NegPowerCache_valid : CutTop2H7NegPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
