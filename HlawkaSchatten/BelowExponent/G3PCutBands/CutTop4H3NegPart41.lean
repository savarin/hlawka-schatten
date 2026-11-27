/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H3NegPart41`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H3NegPart41Box : Box := (((((((((⟨![27/136, 19/100, 0, -8], ![9/34, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).upperChild 2 (5/16)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H3NegPart41Tree : CertTree :=
  .cut 3 (3/16)
    (.cut 2 (13/32)
      (.cut 3 (5/32)
        (.row ⟨123862991199, 126950446638, (.direct 14500097491 18316390982), (.chord (.secant 1087069102742 59526045818 5823564528 52669049016) 43500686443 65931360876)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 19358451269 23412458922), (.chord (.secant 1158140314565 85301921414 15534614770 71585865408) 43500686443 65931360876)⟩))
      (.row ⟨123862991199, 126950446638, (.direct 19358451269 23412458922), (.chord (.secant 1044647712727 45577393488 637569701 37899062295) 65931360876 91625974997)⟩))
    (.cut 2 (13/32)
      (.cut 3 (7/32)
        (.row ⟨123862991199, 126950446638, (.direct 24716051037 28955834162), (.chord (.secant 1230859058083 114346064806 28347791509 92562275563) 43500686443 65931360876)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 30541785600 34922204517), (.chord (.secant 1305199260818 146415153112 43795104429 115463424704) 43500686443 65931360876)⟩))
      (.row ⟨123862991199, 126950446638, (.direct 30541785600 34922204517), (.chord (.secant 1153116411151 83389901383 12762537103 66605027304) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H3NegPart41_checked : CutTop4H3NegPart41Tree.commonOK CutTop4H3NegPart41Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
