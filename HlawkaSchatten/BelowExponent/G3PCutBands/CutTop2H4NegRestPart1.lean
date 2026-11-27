/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H4NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H4NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H4NegRestPart1Box : Box := ((⟨![9/34, 17/100, 0, -8], ![45/136, 9/50, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop2H4NegRestPart1Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 308690086938)⟩)))
        (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 308690086938)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 387453046792), (.variance 251247986261)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 593382169971 581589814919), (.variance 225897720491)⟩)))
          (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 387453046792), (.variance 251247986261)⟩)))
        (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 387453046792), (.variance 251247986261)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 803353153030), (.variance 207575547671)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1928364156755), (.variance 165042977878)⟩)))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3378498728526), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 803353153030), (.variance 207575547671)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3378498728526), (.variance 142503688814)⟩))))
      (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 803353153030), (.variance 207575547671)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H4NegRestPart1_ok : CutTop2H4NegRestPart1Tree.geometryOK CutTop2H4NegPowerCache CutTop2H4NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
