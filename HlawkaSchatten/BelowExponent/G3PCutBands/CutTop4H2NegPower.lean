/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2NegPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegPowerCache : PowerCache :=
  ⟨[(23/64, 54287507865), (13/32, 65931360876), (5/16, 43500686443), (1/2, 91625974997), (7/32, 24716235638), (1/8, 10180665226), (17/64, 33622326476), (3/4, 174227471798), (11/64, 16864782083), (19/128, 13368036905), (25/128, 20652546629), (5/8, 130502050762), (0, 0), (1, 274877906944), (29/64, 78389578142), (49/128, 60005146086), (43/128, 48783993063)], [((1/5, 63475223319/137438953472), (12, 25)), ((123862991199/274877906944, 19/100), (25, 12)), ((125417011705/274877906944, 39/200), (25, 12)), ((39/200, 62708505853/137438953472), (12, 25)), ((126186252621/274877906944, 79/400), (25, 12)), ((79/400, 63093126311/137438953472), (12, 25)), ((62321312603/137438953472, 77/400), (25, 12)), ((77/400, 124642625207/274877906944), (12, 25)), ((159/800, 126568974447/274877906944), (12, 25)), ((63284487223/137438953472, 159/800), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutTop4H2NegPowerCache_valid : CutTop4H2NegPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
