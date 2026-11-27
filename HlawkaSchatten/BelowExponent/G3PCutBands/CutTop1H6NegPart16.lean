/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H6NegPart16`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H6NegPart16Box : Box := (((((((((⟨![27/68, 4/25, 0, -8], ![63/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).upperChild 2 (5/16)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutTop1H6NegPart16Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 3 (3/16)
      (.cut 2 (23/64)
        (.cut 3 (5/32)
          (.row ⟨114055813619, 117423580140, (.direct 14500097491 20192964482), (.chord (.secant 972362226831 24784083081 1136572743 72647477010) 43500686443 54287507865)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 19358451269 25384668494), (.chord (.secant 1039655932039 44014832064 2582771178 96270467298) 43500686443 54287507865)⟩))
        (.cut 3 (5/32)
          (.row ⟨114055813619, 117423580140, (.direct 14500097491 20192964482), (.chord (.secant 917138713671 12012773761 5136129754 59817483682) 54287507865 65931360876)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 19358451269 25384668494), (.chord (.secant 974336791472 25295501549 103471936 79268507919) 54287507865 65931360876)⟩)))
      (.cut 2 (23/64)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 37023311985), (.chord (.secant 1179158474759 93438767973 11713401706 122260777309) 43500686443 54287507865)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 37023311985), (.chord (.secant 1092515063940 61399159789 3820931474 100668768589) 54287507865 65931360876)⟩)))
    (.cut 3 (3/16)
      (.cut 2 (29/64)
        (.row ⟨114055813619, 117423580140, (.direct 19358451269 25384668494), (.chord (.secant 925163440919 13670009607 9631285422 50310845911) 65931360876 78389578142)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 19358451269 25384668494), (.chord (.secant 886836097022 6468786979 13997998162 43042860708) 78389578142 91625974997)⟩))
      (.row ⟨114055813619, 117423580140, (.direct 30541785600 37023311985), (.chord (.secant 1027541090708 40295865268 1182037855 72438215674) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H6NegPart16_checked : CutTop1H6NegPart16Tree.commonOK CutTop1H6NegPart16Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
