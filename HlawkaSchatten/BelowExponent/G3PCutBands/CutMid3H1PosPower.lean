/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H1PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H1PosPowerCache : PowerCache :=
  ⟨[(7/32, 24716235638), (11/64, 16864782083), (1/8, 10180665226), (5/16, 43500686443), (17/64, 33622326476), (1/16, 3393555298), (1/2, 91625974997), (0, 0), (1, 274877906944)], [((13/100, 25809087679/68719476736), (12, 25)), ((5955090165/17179869184, 11/100), (25, 12)), ((51139294017/137438953472, 51/400), (25, 12)), ((99345187399/274877906944, 3/25), (25, 12)), ((25327752295/68719476736, 1/8), (25, 12)), ((51/400, 102278588035/274877906944), (12, 25)), ((50166657071/137438953472, 49/400), (25, 12)), ((1/8, 101311009181/274877906944), (12, 25)), ((49/400, 100333314143/274877906944), (12, 25)), ((3/25, 12418148425/34359738368), (12, 25)), ((98346296769/274877906944, 47/400), (25, 12)), ((23/200, 1520879565/4294967296), (12, 25)), ((97336292159/274877906944, 23/200), (25, 12)), ((47/400, 49173148385/137438953472), (12, 25)), ((9/80, 48157402091/137438953472), (12, 25)), ((96314804181/274877906944, 9/80), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutMid3H1PosPowerCache_valid : CutMid3H1PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
