/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H6NegPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H6NegPart5Box : Box := (((((((((⟨![27/68, 4/25, 0, -8], ![63/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).upperChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop1H6NegPart5Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 0 (117/272)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 5023140204), (.chord (.midpoint ⟨471677357217, 120422954662, 159782074246, 403932799119, 202699694319, 259782764907⟩) 43500686443 65931360876)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 4683575983), (.chord (.midpoint ⟨458675853093, 128413620449, 161672030433, 400576768303, 207563447686, 256153045994⟩) 43500686443 65931360876)⟩))
    (.cut 0 (117/272)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 5023140204), (.chord (.midpoint ⟨491473056182, 108771533466, 150875567097, 420709618800, 195228091330, 284519263349⟩) 65931360876 91625974997)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 4683575983), (.chord (.midpoint ⟨477418273591, 116980574553, 153232007494, 416108914622, 200541581133, 280698339905⟩) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H6NegPart5_checked : CutTop1H6NegPart5Tree.commonOK CutTop1H6NegPart5Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
