/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7PosPowerCache : PowerCache :=
  ⟨[(1/8, 10180665226), (1/2, 91625974997), (5/16, 43500686443), (1, 274877906944), (0, 0), (13/32, 65931360876), (3/4, 174227471798), (7/32, 24716235638), (5/8, 130502050762)], [((123862991199/274877906944, 19/100), (25, 12)), ((1/5, 63475223319/137438953472), (12, 25)), ((77/400, 124642625207/274877906944), (12, 25)), ((62321312603/137438953472, 77/400), (25, 12)), ((39/200, 62708505853/137438953472), (12, 25)), ((125417011705/274877906944, 39/200), (25, 12)), ((79/400, 63093126311/137438953472), (12, 25)), ((126186252621/274877906944, 79/400), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutTop4H7PosPowerCache_valid : CutTop4H7PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
