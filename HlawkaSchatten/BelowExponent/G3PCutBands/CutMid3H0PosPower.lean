/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H0PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H0PosPowerCache : PowerCache :=
  ⟨[(1/8, 10180665226), (7/32, 24716235638), (1/16, 3393555298), (5/16, 43500686443), (1/2, 91625974997), (0, 0), (1, 274877906944)], [((5955090165/17179869184, 11/100), (25, 12)), ((13/100, 25809087679/68719476736), (12, 25)), ((3/25, 12418148425/34359738368), (12, 25)), ((99345187399/274877906944, 3/25), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutMid3H0PosPowerCache_valid : CutMid3H0PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
