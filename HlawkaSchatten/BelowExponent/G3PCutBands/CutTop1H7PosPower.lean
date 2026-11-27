/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H7PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H7PosPowerCache : PowerCache :=
  ⟨[(1/8, 10180665226), (1/2, 91625974997), (5/16, 43500686443), (1, 274877906944), (0, 0), (3/4, 174227471798), (7/32, 24716235638)], [((114055813619/274877906944, 4/25), (25, 12)), ((17/100, 29355895035/68719476736), (12, 25)), ((13/80, 114907784327/274877906944), (12, 25)), ((57453892163/137438953472, 13/80), (25, 12)), ((33/200, 28938241531/68719476736), (12, 25)), ((115752966123/274877906944, 33/200), (25, 12)), ((67/400, 116591514757/274877906944), (12, 25)), ((29147878689/68719476736, 67/400), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutTop1H7PosPowerCache_valid : CutTop1H7PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
