/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H5PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H5PosPowerCache : PowerCache :=
  ⟨[(1/8, 10180665226), (1/2, 91625974997), (5/16, 43500686443), (1, 274877906944), (0, 0), (7/32, 24716235638)], [((123862991199/274877906944, 19/100), (25, 12)), ((1/5, 63475223319/137438953472), (12, 25)), ((39/200, 62708505853/137438953472), (12, 25)), ((125417011705/274877906944, 39/200), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutTop4H5PosPowerCache_valid : CutTop4H5PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
