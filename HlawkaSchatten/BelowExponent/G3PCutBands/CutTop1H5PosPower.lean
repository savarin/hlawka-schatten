/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H5PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H5PosPowerCache : PowerCache :=
  ⟨[(5/16, 43500686443), (23/64, 54287507865), (7/32, 24716235638), (13/32, 65931360876), (1/2, 91625974997), (1/8, 10180665226), (1, 274877906944), (0, 0)], [((114055813619/274877906944, 4/25), (25, 12)), ((17/100, 29355895035/68719476736), (12, 25)), ((33/200, 28938241531/68719476736), (12, 25)), ((115752966123/274877906944, 33/200), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutTop1H5PosPowerCache_valid : CutTop1H5PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
