/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2NegPart32`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegPart32Box : Box := ((((((((((⟨![9/68, 19/100, 0, -8], ![27/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).upperChild 2 (5/16)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutTop4H2NegPart32Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 3 (3/32)
      (.cut 0 (45/272)
        (.row ⟨123862991199, 126950446638, (.direct 6452795533 8362535096), (.chord (.secant 973630795853 25112247810 578380068 19098559953) 43500686443 65931360876)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 6452795533 8766024539), (.chord (.secant 958094436214 21194109732 54402176 20420039234) 43500686443 65931360876)⟩))
      (.row ⟨123862991199, 126950446638, (.direct 10180561190 12782493823), (.chord (.secant 1050057697816 47290300948 3456834392 32850452855) 43500686443 65931360876)⟩))
    (.cut 3 (3/32)
      (.cut 0 (45/272)
        (.row ⟨123862991199, 126950446638, (.direct 6452795533 8362535096), (.chord (.secant 917591269352 12104259864 330967612 13742748862) 65931360876 91625974997)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 6452795533 8766024539), (.chord (.secant 900731143973 8863288263 1737384462 14693645575) 65931360876 91625974997)⟩))
      (.row ⟨123862991199, 126950446638, (.direct 10180561190 12782493823), (.chord (.secant 974947673945 25454423789 322310244 23638197052) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H2NegPart32_checked : CutTop4H2NegPart32Tree.commonOK CutTop4H2NegPart32Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
