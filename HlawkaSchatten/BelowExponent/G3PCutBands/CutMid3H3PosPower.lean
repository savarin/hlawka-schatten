/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3PosPowerCache : PowerCache :=
  ⟨[(1/8, 10180665226), (7/32, 24716235638), (5/16, 43500686443), (1/2, 91625974997), (17/64, 33622326476), (0, 0), (1, 274877906944)], [((5955090165/17179869184, 11/100), (25, 12)), ((13/100, 25809087679/68719476736), (12, 25)), ((3/25, 12418148425/34359738368), (12, 25)), ((99345187399/274877906944, 3/25), (25, 12)), ((23/200, 1520879565/4294967296), (12, 25)), ((97336292159/274877906944, 23/200), (25, 12)), ((1/8, 101311009181/274877906944), (12, 25)), ((25327752295/68719476736, 1/8), (25, 12)), ((89/800, 23949908213/68719476736), (12, 25)), ((95799632851/274877906944, 89/800), (25, 12)), ((9/80, 48157402091/137438953472), (12, 25)), ((96314804181/274877906944, 9/80), (25, 12)), ((91/800, 96827007473/274877906944), (12, 25)), ((6051687967/17179869184, 91/800), (25, 12)), ((93/800, 48921353165/137438953472), (12, 25)), ((97842706329/274877906944, 93/800), (25, 12)), ((47/400, 49173148385/137438953472), (12, 25)), ((98346296769/274877906944, 47/400), (25, 12)), ((19/160, 98847109017/274877906944), (12, 25)), ((49/400, 100333314143/274877906944), (12, 25)), ((50166657071/137438953472, 49/400), (25, 12)), ((51/400, 102278588035/274877906944), (12, 25)), ((51139294017/137438953472, 51/400), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutMid3H3PosPowerCache_valid : CutMid3H3PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
