/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1PosPowerCache : PowerCache :=
  ⟨[(11/64, 16864782083), (1/8, 10180665226), (7/32, 24716235638), (1/16, 3393555298), (5/16, 43500686443), (1/2, 91625974997), (0, 0), (1, 274877906944)], [((10816487501/34359738368, 9/100), (25, 12)), ((11/100, 95281442641/274877906944), (12, 25)), ((1/10, 45510314799/137438953472), (12, 25)), ((91020629597/274877906944, 1/10), (25, 12)), ((21/200, 93177423805/274877906944), (12, 25)), ((23294355951/68719476736, 21/200), (25, 12)), ((19/200, 88806993133/274877906944), (12, 25)), ((22201748283/68719476736, 19/200), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutMid2H1PosPowerCache_valid : CutMid2H1PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
