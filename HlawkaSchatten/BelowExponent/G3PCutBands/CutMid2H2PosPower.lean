/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H2PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H2PosPowerCache : PowerCache :=
  ⟨[(7/32, 24716235638), (5/16, 43500686443), (11/64, 16864782083), (1/8, 10180665226), (1/16, 3393555298), (17/64, 33622326476), (1/2, 91625974997), (0, 0), (1, 274877906944)], [((11/100, 95281442641/274877906944), (12, 25)), ((10816487501/34359738368, 9/100), (25, 12)), ((23294355951/68719476736, 21/200), (25, 12)), ((1/10, 45510314799/137438953472), (12, 25)), ((91020629597/274877906944, 1/10), (25, 12)), ((21/200, 93177423805/274877906944), (12, 25)), ((19/200, 88806993133/274877906944), (12, 25)), ((22201748283/68719476736, 19/200), (25, 12)), ((37/400, 21919360309/68719476736), (12, 25)), ((87677441235/274877906944, 37/400), (25, 12)), ((39/400, 89921191063/274877906944), (12, 25)), ((44960595531/137438953472, 39/400), (25, 12)), ((94235794855/274877906944, 43/400), (25, 12)), ((43/400, 11779474357/34359738368), (12, 25)), ((41/400, 2878308315/8589934592), (12, 25)), ((92105866079/274877906944, 41/400), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutMid2H2PosPowerCache_valid : CutMid2H2PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
