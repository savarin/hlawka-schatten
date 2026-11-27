/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H5PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H5PosPowerCache : PowerCache :=
  ⟨[(1/8, 10180665226), (1/2, 91625974997), (5/16, 43500686443), (0, 0), (1, 274877906944), (7/32, 24716235638)], [((60344909737/137438953472, 9/50), (25, 12)), ((19/100, 3870718475/8589934592), (12, 25)), ((37/200, 61143777923/137438953472), (12, 25)), ((122287555845/274877906944, 37/200), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutTop3H5PosPowerCache_valid : CutTop3H5PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
