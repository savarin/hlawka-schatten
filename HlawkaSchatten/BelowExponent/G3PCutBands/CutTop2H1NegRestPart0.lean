/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H1NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H1NegRestPart0Box : Box := (((⟨![9/136, 17/100, 0, -8], ![9/68, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop2H1NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3436261993017), (.variance 141872490250)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 799121175227), (.variance 207862838555)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5213208867914), (.variance 127203006982)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3436261993017), (.variance 141872490250)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1948886916798), (.variance 164586096861)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 799121175227), (.variance 207862838555)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5213208867914), (.variance 127203006982)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3436261993017), (.variance 141872490250)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1948886916798), (.variance 164586096861)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 799121175227), (.variance 207862838555)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 27434943132), (.variance 502595125732)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨117423580139, 120689819475, (.direct 331294831298 318406198368), (.variance 264498083633)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨117423580139, 120689819475, (.direct 151782739331 144126542896), (.variance 325509883447)⟩))
            (.cut 2 (5/16)
              (.cut 3 (-15/32)
                (.original (.row ⟨117423580139, 120689819475, (.direct 82716570280 77404576742), (.variance 383054289788)⟩))
                (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 27434943132), (.variance 502595125732)⟩)))
              (.cut 3 (-15/32)
                (.original (.row ⟨117423580139, 120689819475, (.direct 82716570280 77404576742), (.variance 383054289788)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨117423580139, 120689819475, (.direct 54287234842 50089288522), (.chord (.midpoint ⟨391835019745, 173983705836, 226129991827, 315713686634, 232183079336, 160011494190⟩) 43500686443 91625974997)⟩))
                  (.cut 2 (13/32)
                    (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 27434943132), (.chord (.midpoint ⟨446831872101, 135931997135, 205500837937, 337885661579, 211968278703, 231284722604⟩) 43500686443 65931360876)⟩))
                    (.covered))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨117423580139, 120689819475, (.direct 331294831298 318406198368), (.variance 264498083633)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨117423580139, 120689819475, (.direct 151782739331 144126542896), (.variance 325509883447)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨117423580139, 120689819475, (.direct 82716570280 77404576742), (.variance 383054289788)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop2H1NegRestPart0_ok : CutTop2H1NegRestPart0Tree.ok CutTop2H1NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
