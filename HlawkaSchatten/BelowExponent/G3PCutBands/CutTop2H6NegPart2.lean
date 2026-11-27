/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H6NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H6NegPart2Box : Box := ((((((((⟨![27/68, 17/100, 0, -8], ![63/136, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop2H6NegPart2Tree : CertTree :=
  .cut 2 (5/16)
    (.cut 2 (7/32)
      (.cut 3 (-3/16)
        (.row ⟨117423580139, 120689819475, (.direct 19358451269 11245291040), (.variance 634812142917)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 4383904608), (.chord (.midpoint ⟨400044216341, 167962379851, 190512610290, 356537738537, 229184389530, 157789745743⟩) 10180665226 24716235638)⟩))
      (.cut 3 (-3/16)
        (.row ⟨117423580139, 120689819475, (.direct 19358451269 11245291040), (.chord (.midpoint ⟨355909340504, 201846424997, 208692724642, 334210812650, 245267683433, 204804559126⟩) 24716235638 43500686443)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 4383904608), (.chord (.midpoint ⟨451614730221, 132868152045, 168596716711, 388832500841, 210192280616, 255048309672⟩) 24716235638 43500686443)⟩)))
    (.cut 2 (13/32)
      (.cut 0 (117/272)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 4737202499), (.chord (.midpoint ⟨475486598186, 118133023693, 158085545020, 407003683204, 201268488604, 261358264048⟩) 43500686443 65931360876)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 4383904608), (.chord (.midpoint ⟨462736589649, 125888673418, 159859796086, 403793450364, 206047731519, 257876556656⟩) 43500686443 65931360876)⟩))
      (.cut 0 (117/272)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 4737202499), (.chord (.midpoint ⟨494614412578, 106978697107, 149440452064, 423572193121, 194034236048, 285656269072⟩) 65931360876 91625974997)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 4383904608), (.chord (.midpoint ⟨480765620736, 114997453020, 151703146212, 419079941409, 199280075412, 281941778216⟩) 65931360876 91625974997)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H6NegPart2_checked : CutTop2H6NegPart2Tree.commonOK CutTop2H6NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
