/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H1NegPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H1NegPart9Box : Box := (((((((⟨![9/68, 7/100, 0, -8], ![9/34, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 2 (5/16)

set_option maxRecDepth 16000 in
def CutMid1H1NegPart9Tree : CertTree :=
  .cut 3 (0)
    (.cut 1 (2/25)
      (.row ⟨76698504228, 81775466253, (.direct 0 217099539), (.chord .universal 43500686443 91625974997)⟩)
      (.cut 3 (-1/8)
        (.row ⟨81775466252, 86531900009, (.direct 10180561190 8429717858), (.chord (.midpoint ⟨605415247587, 53074466721, 132740555830, 460725371221, 149805753292, 267958549466⟩) 43500686443 91625974997)⟩)
        (.cut 0 (27/136)
          (.row ⟨81775466252, 86531900009, (.direct 0 167226462), (.chord .universal 43500686443 91625974997)⟩)
          (.cut 1 (17/200)
            (.row ⟨81775466252, 84190079492, (.direct 0 239985040), (.chord .universal 43500686443 91625974997)⟩)
            (.row ⟨84190079491, 86531900009, (.direct 0 263832444), (.chord .universal 43500686443 91625974997)⟩)))))
    (.cut 3 (1/8)
      (.cut 1 (2/25)
        (.row ⟨76698504228, 81775466253, (.direct 10180561190 11454296155), (.chord .universal 43500686443 91625974997)⟩)
        (.cut 3 (1/16)
          (.cut 3 (1/32)
            (.row ⟨81775466252, 86531900009, (.direct 1131165907 1899122977), (.chord (.secant 828766237941 89668966 31256930468 217094729) 43500686443 91625974997)⟩)
            (.row ⟨81775466252, 86531900009, (.direct 3393509060 4453608755), (.chord (.secant 894345862997 7730201354 20020748809 4357962786) 43500686443 91625974997)⟩))
          (.row ⟨81775466252, 86531900009, (.direct 10180561190 11625075029), (.chord (.secant 1030945796991 41330384776 10749967368 11547263516) 43500686443 91625974997)⟩)))
      (.row ⟨76698504228, 86531900009, (.direct 30541785600 32373100089), (.chord (.secant 1325014641509 155325879511 89484925 32184322666) 43500686443 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutMid1H1NegPart9_checked : CutMid1H1NegPart9Tree.commonOK CutMid1H1NegPart9Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
