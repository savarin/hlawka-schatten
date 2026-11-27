/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H2NegPart26`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H2NegPart26Box : Box := (((((((((⟨![9/34, 13/100, 0, -8], ![27/68, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 2 (5/16)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutMid4H2NegPart26Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 3 (3/16)
      (.cut 2 (23/64)
        (.cut 0 (45/136)
          (.row ⟨103236350715, 110576703735, (.direct 19358451269 23045068111), (.chord (.secant 1104608635650 65622071102 3329121741 62462397950) 43500686443 54287507865)⟩)
          (.row ⟨103236350715, 110576703735, (.direct 19358451269 23810503769), (.chord (.secant 1066832785610 52726654979 100241853 65310231965) 43500686443 54287507865)⟩))
        (.cut 0 (45/136)
          (.row ⟨103236350715, 110576703735, (.direct 19358451269 23045068111), (.chord (.secant 1041694076024 44650728425 408905654 51431152518) 54287507865 65931360876)⟩)
          (.row ⟨103236350715, 110576703735, (.direct 19358451269 23810503769), (.chord (.secant 1003457200277 33225369128 1661110357 53776041449) 54287507865 65931360876)⟩)))
      (.cut 2 (23/64)
        (.row ⟨103236350715, 110576703735, (.direct 30541785600 35347683971), (.chord (.secant 1259436130621 126408694877 16003709679 110693944452) 43500686443 54287507865)⟩)
        (.row ⟨103236350715, 110576703735, (.direct 30541785600 35347683971), (.chord (.secant 1173134174774 91084188300 7293855900 91144709885) 54287507865 65931360876)⟩)))
    (.cut 3 (3/16)
      (.cut 0 (45/136)
        (.row ⟨103236350715, 110576703735, (.direct 19358451269 23045068111), (.chord (.secant 994230896060 30636559583 2283617114 37008309237) 65931360876 91625974997)⟩)
        (.row ⟨103236350715, 110576703735, (.direct 19358451269 23810503769), (.chord (.secant 955688158509 20607404126 7933964906 38695620729) 65931360876 91625974997)⟩))
      (.row ⟨103236350715, 110576703735, (.direct 30541785600 35347683971), (.chord (.secant 1108298759802 66927687804 126502867 65584989712) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutMid4H2NegPart26_checked : CutMid4H2NegPart26Tree.commonOK CutMid4H2NegPart26Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
