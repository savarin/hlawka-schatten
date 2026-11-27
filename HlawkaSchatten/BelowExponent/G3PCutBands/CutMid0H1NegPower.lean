/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryCheckData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H1NegPower`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H1NegPowerCache : PowerCache :=
  ⟨[(1/8, 10180665226), (1/16, 3393555298), (7/32, 24716235638), (11/64, 16864782083), (3/32, 6452870597), (5/16, 43500686443), (0, 0), (19/128, 13368036905), (1/2, 91625974997), (1, 274877906944)], [((7/100, 76698504229/274877906944), (12, 25)), ((8157469343/34359738368, 1/20), (25, 12)), ((35614138209/137438953472, 3/50), (25, 12)), ((37009076723/137438953472, 13/200), (25, 12)), ((3/50, 71228276419/274877906944), (12, 25)), ((13/200, 74018153447/274877906944), (12, 25)), ((17078665589/68719476736, 11/200), (25, 12)), ((11/200, 68314662357/274877906944), (12, 25)), ((75371237551/274877906944, 27/400), (25, 12)), ((27/400, 4710702347/17179869184), (12, 25)), ((72637726647/274877906944, 1/16), (25, 12)), ((1/16, 9079715831/34359738368), (12, 25)), ((23/400, 69787943483/274877906944), (12, 25)), ((34893971741/137438953472, 23/400), (25, 12)), ((21/400, 66806127931/274877906944), (12, 25)), ((33403063965/137438953472, 21/400), (25, 12)), ((53/800, 74698014607/274877906944), (12, 25)), ((37349007303/137438953472, 53/800), (25, 12)), ((11/160, 76038008261/274877906944), (12, 25)), ((19009502065/68719476736, 11/160), (25, 12))]⟩

set_option maxRecDepth 16000 in
theorem CutMid0H1NegPowerCache_valid : CutMid0H1NegPowerCache.valid = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
