/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H6PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H6PosPowerCache : PowerCache :=
  ⟨[(1/8, 10180665226), (1/2, 91625974997), (5/16, 43500686443), (0, 0), (1, 274877906944), (7/32, 24716235638)], [((55288351867/137438953472, 3/20), (25, 12)), ((4/25, 28513953405/68719476736), (12, 25))]⟩

set_option maxRecDepth 16000 in
theorem CutTop0H6PosPowerCache_valid : CutTop0H6PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
