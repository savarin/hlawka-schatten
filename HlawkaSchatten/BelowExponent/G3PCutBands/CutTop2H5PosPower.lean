/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H5PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H5PosPowerCache : PowerCache :=
  ⟨[(5/16, 43500686443), (13/32, 65931360876), (1/2, 91625974997), (1/8, 10180665226), (1, 274877906944), (7/32, 24716235638), (0, 0), (3/4, 174227471798)], [((117423580139/274877906944, 17/100), (25, 12)), ((9/50, 120689819475/274877906944), (12, 25)), ((7/40, 119068833411/274877906944), (12, 25)), ((59534416705/137438953472, 7/40), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutTop2H5PosPowerCache_valid : CutTop2H5PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
