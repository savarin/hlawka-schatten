/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H7NegRestPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H7NegRestPart3Box : Box := ((⟨![63/136, 17/100, 0, -8], ![9/17, 9/50, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop2H7NegRestPart3Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 307912233455)⟩)))
        (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 307912233455)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 385028422461), (.variance 251661328111)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 488587506629 476305647429), (.variance 238025161638)⟩)))
            (.original (.row ⟨117423580139, 120689819475, (.direct 593382169971 574555577717), (.variance 226618671653)⟩)))
          (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 385028422461), (.variance 251661328111)⟩)))
        (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 385028422461), (.variance 251661328111)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 790681997305), (.variance 208441511949)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 1366046989981 1294618117835), (.variance 183193679655)⟩)))
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1884657487211), (.variance 166036759005)⟩)))
          (.cut 3 (13/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3292533498421), (.variance 143468713204)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 4970365599638), (.chord .universal 0 10180665226)⟩))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 790681997305), (.variance 208441511949)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1884657487211), (.variance 166036759005)⟩)))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3292533498421), (.variance 143468713204)⟩))))
      (.cut 3 (5)
        (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 790681997305), (.variance 208441511949)⟩))
        (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3292533498421), (.variance 143468713204)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop2H7NegRestPart3_ok : CutTop2H7NegRestPart3Tree.ok CutTop2H7NegRestPart3Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
