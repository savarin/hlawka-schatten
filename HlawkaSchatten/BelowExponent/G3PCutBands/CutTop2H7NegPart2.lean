/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H7NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H7NegPart2Box : Box := ((((((((⟨![63/136, 17/100, 0, -8], ![9/17, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop2H7NegPart2Tree : CertTree :=
  .cut 2 (5/16)
    (.cut 2 (7/32)
      (.cut 3 (-3/16)
        (.row ⟨117423580139, 120689819475, (.direct 19358451269 10222418736), (.variance 650864631859)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 3708159441), (.chord (.midpoint ⟨383895725688, 179926476735, 190393415649, 356696093000, 235079109785, 155928439485⟩) 10180665226 24716235638)⟩))
      (.row ⟨117423580139, 120689819475, (.direct 10180561190 3708159441), (.chord (.midpoint ⟨429518941506, 147342544998, 170753764309, 385341001637, 218368900067, 198585972858⟩) 24716235638 43500686443)⟩))
    (.cut 2 (13/32)
      (.cut 0 (135/272)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 4040816802), (.chord (.midpoint ⟨450114941782, 133824831730, 161620183930, 400667937658, 210749581820, 254361172155⟩) 43500686443 65931360876)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 3708159441), (.chord (.midpoint ⟨437622587566, 141938631015, 163367071058, 397623399026, 215378152730, 250810973350⟩) 43500686443 65931360876)⟩))
      (.cut 0 (135/272)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 4040816802), (.chord (.midpoint ⟨467062522046, 123228118726, 153942144017, 414746082745, 204429710944, 278192235829⟩) 65931360876 91625974997)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 3708159441), (.chord (.midpoint ⟨453506223974, 131666891184, 156158270813, 410561317028, 209488904712, 274406483933⟩) 65931360876 91625974997)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H7NegPart2_checked : CutTop2H7NegPart2Tree.commonOK CutTop2H7NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
