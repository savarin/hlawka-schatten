/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H6NegPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H6NegPowerCache : PowerCache :=
  ⟨[(13/32, 65931360876), (5/16, 43500686443), (1/2, 91625974997), (7/32, 24716235638), (1/8, 10180665226), (23/64, 54287507865), (3/4, 174227471798), (11/64, 16864782083), (17/64, 33622326476), (1, 274877906944), (0, 0), (19/128, 13368036905), (25/128, 20652546629)], [((19/100, 3870718475/8589934592), (12, 25)), ((60344909737/137438953472, 9/50), (25, 12)), ((122287555845/274877906944, 37/200), (25, 12)), ((37/200, 61143777923/137438953472), (12, 25)), ((123078004367/274877906944, 3/16), (25, 12)), ((3/16, 7692375273/17179869184), (12, 25)), ((73/400, 30372883261/68719476736), (12, 25)), ((121491533043/274877906944, 73/400), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutTop3H6NegPowerCache_valid : CutTop3H6NegPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
