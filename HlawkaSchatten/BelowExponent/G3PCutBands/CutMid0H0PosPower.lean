/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H0PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H0PosPowerCache : PowerCache :=
  ⟨[(1/16, 3393555298), (1/8, 10180665226), (5/16, 43500686443), (1/2, 91625974997), (0, 0), (1, 274877906944)], [((8157469343/34359738368, 1/20), (25, 12)), ((7/100, 76698504229/274877906944), (12, 25))]⟩

set_option maxRecDepth 16000 in
theorem CutMid0H0PosPowerCache_valid : CutMid0H0PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
