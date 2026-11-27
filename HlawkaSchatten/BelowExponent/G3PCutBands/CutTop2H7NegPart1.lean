/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H7NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H7NegPart1Box : Box := ((((((⟨![63/136, 17/100, 0, -8], ![9/17, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop2H7NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨117423580139, 120689819475, (.direct 10180561190 3708159441), (.variance 848813725125)⟩)
      (.row ⟨117423580139, 120689819475, (.direct 0 2563271455), (.chord .universal 0 10180665226)⟩))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.row ⟨117423580139, 120689819475, (.direct 1131165907 5216153935), (.variance 1014295304428)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 3393509060 8504383637), (.variance 814810661529)⟩))
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 16700147583), (.variance 706519314882)⟩))
      (.cut 3 (3/16)
        (.row ⟨117423580139, 120689819475, (.direct 19358451269 26768755827), (.variance 584110430723)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 30541785600 38487961339), (.variance 512922167230)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H7NegPart1_checked : CutTop2H7NegPart1Tree.commonOK CutTop2H7NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
