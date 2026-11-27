/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H0PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H0PosPowerCache : PowerCache :=
  ⟨[(1/8, 10180665226), (0, 0), (1/2, 91625974997), (7/32, 24716235638), (5/16, 43500686443), (1, 274877906944)], [((123862991199/274877906944, 19/100), (25, 12)), ((1/5, 63475223319/137438953472), (12, 25))]⟩

set_option maxRecDepth 16000 in
theorem CutTop4H0PosPowerCache_valid : CutTop4H0PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
