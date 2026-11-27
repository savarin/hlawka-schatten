/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H2NegRestPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H2NegRestPart3Box : Box := ((⟨![9/68, 17/100, 0, -8], ![27/136, 9/50, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop2H2NegRestPart3Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 309212394581)⟩)))
        (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 309212394581)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 389072581854), (.variance 250973707235)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 593382169971 586296835396), (.variance 225421406536)⟩)))
          (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 389072581854), (.variance 250973707235)⟩)))
        (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 389072581854), (.variance 250973707235)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 811841829266), (.variance 207005003013)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1957706910725), (.variance 164391606018)⟩)))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3436261993017), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 811841829266), (.variance 207005003013)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3436261993017), (.variance 141872490250)⟩))))
      (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 811841829266), (.variance 207005003013)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H2NegRestPart3_ok : CutTop2H2NegRestPart3Tree.geometryOK CutTop2H2NegPowerCache CutTop2H2NegRestPart3Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
