/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H6NegPart18`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H6NegPart18Box : Box := (((((((((⟨![27/68, 17/100, 0, -8], ![63/136, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).upperChild 2 (5/16)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutTop2H6NegPart18Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 3 (3/16)
      (.cut 2 (23/64)
        (.cut 3 (5/32)
          (.row ⟨117423580139, 120689819475, (.direct 14500097491 20584455022), (.chord (.secant 977583400316 26143888173 824716032 74184303460) 43500686443 54287507865)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 19358451269 25794636298), (.chord (.secant 1044809055448 45628186831 3026686810 97913456851) 43500686443 54287507865)⟩))
        (.cut 3 (5/32)
          (.row ⟨117423580139, 120689819475, (.direct 14500097491 20584455022), (.chord (.secant 921581510614 12921186095 4636145360 61082897086) 54287507865 65931360876)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 19358451269 25794636298), (.chord (.secant 978711355438 26440805247 14639381 80621335365) 54287507865 65931360876)⟩)))
      (.cut 2 (23/64)
        (.row ⟨117423580139, 120689819475, (.direct 30541785600 37457952010), (.chord (.secant 1184140797215 95399406721 12446497470 123987882988) 43500686443 54287507865)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 30541785600 37457952010), (.chord (.secant 1096726901486 62860043403 4253619543 102090856733) 54287507865 65931360876)⟩)))
    (.cut 3 (3/16)
      (.cut 2 (29/64)
        (.cut 3 (5/32)
          (.row ⟨117423580139, 120689819475, (.direct 14500097491 20584455022), (.chord (.secant 879338278076 5290567598 9061705718 51375150439) 65931360876 78389578142)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 19358451269 25794636298), (.chord (.secant 928959716377 14479304643 2361878834 67808395322) 65931360876 78389578142)⟩))
        (.cut 3 (5/32)
          (.row ⟨117423580139, 120689819475, (.direct 14500097491 20584455022), (.chord (.secant 846357960345 1237849869 13403541195 43953414104) 78389578142 91625974997)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 19358451269 25794636298), (.chord (.secant 890186718303 7021826265 5888679789 58012686169) 78389578142 91625974997)⟩)))
      (.row ⟨117423580139, 120689819475, (.direct 30541785600 37457952010), (.chord (.secant 1031183372479 41402885484 966498001 73461507497) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop2H6NegPart18_checked : CutTop2H6NegPart18Tree.commonOK CutTop2H6NegPart18Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
