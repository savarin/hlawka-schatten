/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H0NegPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H0NegPart4Box : Box := ((((⟨![0, 7/100, 0, -8], ![9/68, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid1H0NegPart4Tree : CertTree :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.row ⟨76698504228, 86531900009, (.direct 58075547817 59035498538), (.variance 488671898726)⟩)
          (.row ⟨76698504228, 86531900009, (.direct 91625662891 92533317161), (.variance 412983663964)⟩))
        (.cut 3 (5/8)
          (.row ⟨76698504228, 86531900009, (.direct 130501749339 131276878385), (.variance 366503899985)⟩)
          (.row ⟨76698504228, 86531900009, (.direct 174227225485 174801880471), (.variance 334085249950)⟩)))
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.row ⟨76698504228, 86531900009, (.direct 58075547817 59035498538), (.variance 488671898726)⟩)
          (.row ⟨76698504228, 86531900009, (.direct 91625662891 92533317161), (.variance 412983663964)⟩))
        (.row ⟨76698504228, 86531900009, (.direct 174227225485 174801880471), (.variance 366503899985)⟩)))
    (.row ⟨76698504228, 86531900009, (.direct 174227225485 174801880471), (.chord .universal 91625974997 274877906944)⟩)

set_option maxRecDepth 16000 in
theorem CutMid1H0NegPart4_checked : CutMid1H0NegPart4Tree.geometryOK CutMid1H0NegPowerCache CutMid1H0NegPart4Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
