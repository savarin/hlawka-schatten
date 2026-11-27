/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H7NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H7NegRestPart0Box : Box := (((⟨![63/136, 17/100, 0, -8], ![9/17, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop2H7NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3179190521514), (.variance 144790805055)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 724368574225), (.variance 213277869378)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 4838221240632), (.variance 129713919369)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3179190521514), (.variance 144790805055)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1792659188339), (.variance 168226962199)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 724368574225), (.variance 213277869378)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 4838221240632), (.variance 129713919369)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3179190521514), (.variance 144790805055)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1792659188339), (.variance 168226962199)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 724368574225), (.variance 213277869378)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 18878216662), (.variance 554280204246)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨117423580139, 120689819475, (.direct 331294831298 280886417403), (.variance 273325891851)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨117423580139, 120689819475, (.direct 151782739331 122049106225), (.variance 339995284754)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨117423580139, 120689819475, (.direct 82716570280 62265150537), (.variance 405519475467)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 18878216662), (.variance 554280204246)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨117423580139, 120689819475, (.direct 54287234842 38262430414), (.chord (.midpoint ⟨257812153924, 292344007886, 242651980197, 300306090692, 281199194933, 98444185393⟩) 43500686443 91625974997)⟩))
                  (.covered)))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨117423580139, 120689819475, (.direct 331294831298 280886417403), (.variance 273325891851)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨117423580139, 120689819475, (.direct 151782739331 122049106225), (.variance 339995284754)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨117423580139, 120689819475, (.direct 82716570280 62265150537), (.variance 405519475467)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop2H7NegRestPart0_ok : CutTop2H7NegRestPart0Tree.ok CutTop2H7NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
