/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H5NegPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H5NegPart6Box : Box := (((((((((⟨![45/136, 17/100, 0, -8], ![27/68, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).upperChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop2H5NegPart6Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 3 (-3/16)
      (.row ⟨117423580139, 120689819475, (.direct 19358451269 12303721675), (.chord (.midpoint ⟨428034576345, 148344552151, 185852667213, 362857623855, 218915809568, 262771778816⟩) 43500686443 65931360876)⟩)
      (.cut 0 (99/272)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 5473620959), (.chord (.midpoint ⟨501368077252, 103175558563, 154493917395, 413694564762, 191459259594, 298724462803⟩) 43500686443 65931360876)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 5100505224), (.chord (.midpoint ⟨488364056977, 110560914439, 156297051295, 410302632091, 196407329447, 295466907300⟩) 43500686443 65931360876)⟩)))
    (.cut 3 (-3/16)
      (.row ⟨117423580139, 120689819475, (.direct 19358451269 12303721675), (.chord (.midpoint ⟨461866381831, 126427516602, 171665444296, 383887886996, 206372795920, 287867730076⟩) 65931360876 91625974997)⟩)
      (.cut 0 (99/272)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 5473620959), (.chord (.midpoint ⟨522744784567, 91593395667, 144840407787, 433073387919, 183227505267, 315301690506⟩) 65931360876 91625974997)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 5100505224), (.chord (.midpoint ⟨508607818086, 99175902008, 147153184074, 428232980093, 188685774520, 311771496779⟩) 65931360876 91625974997)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H5NegPart6_checked : CutTop2H5NegPart6Tree.commonOK CutTop2H5NegPart6Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
