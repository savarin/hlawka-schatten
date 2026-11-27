/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H0PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H0PosPowerCache : PowerCache :=
  ⟨[(7/32, 24716235638), (1/8, 10180665226), (5/16, 43500686443), (1/2, 91625974997), (1, 274877906944), (0, 0)], [((103236350715/274877906944, 13/100), (25, 12)), ((3/20, 110576703735/274877906944), (12, 25)), ((7/50, 3342961031/8589934592), (12, 25)), ((106974752991/274877906944, 7/50), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutMid4H0PosPowerCache_valid : CutMid4H0PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
