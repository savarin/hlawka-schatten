/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3PosPowerCache : PowerCache :=
  ⟨[(1/8, 10180665226), (5/16, 43500686443), (1/2, 91625974997), (7/32, 24716235638), (0, 0), (1, 274877906944), (3/4, 174227471798)], [((3/20, 110576703735/274877906944), (12, 25)), ((103236350715/274877906944, 13/100), (25, 12)), ((106974752991/274877906944, 7/50), (25, 12)), ((7/50, 3342961031/8589934592), (12, 25)), ((53/400, 52092291381/137438953472), (12, 25)), ((104184582761/274877906944, 53/400), (25, 12)), ((27/200, 13140444525/34359738368), (12, 25)), ((105123556199/274877906944, 27/200), (25, 12)), ((11/80, 13256691303/34359738368), (12, 25)), ((106053530423/274877906944, 11/80), (25, 12)), ((57/400, 107887460377/274877906944), (12, 25)), ((13485932547/34359738368, 57/400), (25, 12)), ((29/200, 6799492415/17179869184), (12, 25)), ((108791878639/274877906944, 29/200), (25, 12)), ((59/400, 109688224065/274877906944), (12, 25)), ((1713878501/4294967296, 59/400), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutMid4H3PosPowerCache_valid : CutMid4H3PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
