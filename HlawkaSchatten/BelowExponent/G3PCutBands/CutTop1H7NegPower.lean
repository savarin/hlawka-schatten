/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H7NegPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H7NegPowerCache : PowerCache :=
  ⟨[(5/16, 43500686443), (13/32, 65931360876), (1/2, 91625974997), (7/32, 24716235638), (1/8, 10180665226), (1, 274877906944), (17/64, 33622326476), (3/4, 174227471798), (5/8, 130502050762), (0, 0), (11/64, 16864782083), (19/128, 13368036905)], [((114055813619/274877906944, 4/25), (25, 12)), ((17/100, 29355895035/68719476736), (12, 25)), ((33/200, 28938241531/68719476736), (12, 25)), ((115752966123/274877906944, 33/200), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutTop1H7NegPowerCache_valid : CutTop1H7NegPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
