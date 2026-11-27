/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H4NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H4NegPart1Box : Box := ((((((⟨![9/34, 17/100, 0, -8], ![45/136, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop2H4NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨117423580139, 120689819475, (.direct 0 1216948227), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.cut 1 (7/40)
            (.row ⟨117423580139, 119068833411, (.direct 1131165907 3349507465), (.chord .universal 0 10180665226)⟩)
            (.row ⟨119068833410, 120689819475, (.direct 1131165907 3432534536), (.chord .universal 0 10180665226)⟩))
          (.cut 2 (1/16)
            (.row ⟨117423580139, 120689819475, (.direct 3393509060 6390725873), (.variance 915591555680)⟩)
            (.row ⟨117423580139, 120689819475, (.direct 3393509060 6390725873), (.chord (.secant 1759507499884 379739451577 8276554279 74975782956) 3393555298 10180665226)⟩)))
        (.cut 3 (3/32)
          (.row ⟨117423580139, 120689819475, (.direct 6452795533 9975757094), (.variance 762608714448)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 10180561190 14117346429), (.variance 672002390524)⟩)))
      (.cut 3 (3/16)
        (.row ⟨117423580139, 120689819475, (.direct 19358451269 23886706938), (.variance 609998000820)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 30541785600 35429054793), (.variance 527984047241)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H4NegPart1_checked : CutTop2H4NegPart1Tree.commonOK CutTop2H4NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
