/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H4NegPart18`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H4NegPart18Box : Box := ((((((((((⟨![9/34, 17/100, 0, -8], ![45/136, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).upperChild 2 (5/16)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutTop2H4NegPart18Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 3 (3/32)
      (.cut 2 (23/64)
        (.cut 0 (81/272)
          (.row ⟨117423580139, 120689819475, (.direct 6452795533 9598467183), (.chord (.secant 904899832005 9631782100 3158518910 28262589210) 43500686443 54287507865)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 6452795533 9975757094), (.chord (.secant 888992423483 6822871491 5504375265 29786208172) 43500686443 54287507865)⟩))
        (.cut 0 (81/272)
          (.row ⟨117423580139, 120689819475, (.direct 6452795533 9598467183), (.chord (.secant 871137944768 4101248147 5753201634 23271241321) 54287507865 65931360876)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 6452795533 9975757094), (.chord (.secant 854633634040 2058823585 8699610304 24525779760) 54287507865 65931360876)⟩)))
      (.cut 2 (23/64)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 14117346429), (.chord (.secant 977780201609 26195613066 130574376 45812619125) 43500686443 54287507865)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 14117346429), (.chord (.secant 933531641329 15474887782 2034556063 37721827512) 54287507865 65931360876)⟩)))
    (.cut 3 (3/32)
      (.cut 0 (81/272)
        (.row ⟨117423580139, 120689819475, (.direct 6452795533 9598467183), (.chord (.secant 845491031982 1160815714 10399367209 16745284773) 65931360876 91625974997)⟩)
        (.cut 2 (29/64)
          (.row ⟨117423580139, 120689819475, (.direct 6452795533 9975757094), (.chord (.secant 828545404194 82195328 11598199907 20627961098) 65931360876 78389578142)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 6452795533 9975757094), (.chord (.secant 808067729871 816885804 14172500594 17648012872) 78389578142 91625974997)⟩)))
      (.row ⟨117423580139, 120689819475, (.direct 10180561190 14117346429), (.chord (.secant 900011567766 8732903282 7013837911 27143491623) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop2H4NegPart18_checked : CutTop2H4NegPart18Tree.commonOK CutTop2H4NegPart18Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
