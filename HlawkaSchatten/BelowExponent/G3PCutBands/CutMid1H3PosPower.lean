/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3PosPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3PosPowerCache : PowerCache :=
  ⟨[(7/32, 24716235638), (11/64, 16864782083), (5/16, 43500686443), (1/8, 10180665226), (1/16, 3393555298), (1/2, 91625974997), (17/64, 33622326476), (0, 0), (1, 274877906944)], [((9/100, 86531900009/274877906944), (12, 25)), ((19174626057/68719476736, 7/100), (25, 12)), ((84190079491/274877906944, 17/200), (25, 12)), ((20443866563/68719476736, 2/25), (25, 12)), ((2/25, 81775466253/274877906944), (12, 25)), ((17/200, 21047519873/68719476736), (12, 25)), ((3/40, 39640511157/137438953472), (12, 25)), ((79281022313/274877906944, 3/40), (25, 12)), ((29/400, 78001342659/274877906944), (12, 25)), ((39000671329/137438953472, 29/400), (25, 12)), ((31/400, 80538706897/274877906944), (12, 25)), ((5033669181/17179869184, 31/400), (25, 12)), ((33/400, 82992286623/274877906944), (12, 25)), ((41496143311/137438953472, 33/400), (25, 12)), ((7/80, 10671211159/34359738368), (12, 25)), ((85369689271/274877906944, 7/80), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutMid1H3PosPowerCache_valid : CutMid1H3PosPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
