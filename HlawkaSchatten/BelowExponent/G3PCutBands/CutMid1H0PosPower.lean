/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H0PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H0PosPowerCache : PowerCache :=
  ⟨[(1/16, 3393555298), (1/8, 10180665226), (5/16, 43500686443), (1/2, 91625974997), (0, 0), (1, 274877906944)], [((19174626057/68719476736, 7/100), (25, 12)), ((9/100, 86531900009/274877906944), (12, 25))]⟩

set_option maxRecDepth 16000 in
theorem CutMid1H0PosPowerCache_valid : CutMid1H0PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
