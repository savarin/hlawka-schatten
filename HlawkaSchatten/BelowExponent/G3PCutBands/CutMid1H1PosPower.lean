/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H1PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H1PosPowerCache : PowerCache :=
  ⟨[(1/8, 10180665226), (7/32, 24716235638), (1/16, 3393555298), (5/16, 43500686443), (1/2, 91625974997), (0, 0), (1, 274877906944)], [((19174626057/68719476736, 7/100), (25, 12)), ((9/100, 86531900009/274877906944), (12, 25)), ((2/25, 81775466253/274877906944), (12, 25)), ((20443866563/68719476736, 2/25), (25, 12)), ((17/200, 21047519873/68719476736), (12, 25)), ((84190079491/274877906944, 17/200), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutMid1H1PosPowerCache_valid : CutMid1H1PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
