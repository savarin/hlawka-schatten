/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H2NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H2NegRestPart0Box : Box := (((⟨![9/68, 17/100, 0, -8], ![27/136, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop2H2NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3392905649810), (.variance 142344991624)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 786474820168), (.variance 208732916643)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5149995134922), (.variance 127610017856)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3392905649810), (.variance 142344991624)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1922515249552), (.variance 165174311800)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 786474820168), (.variance 208732916643)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5149995134922), (.variance 127610017856)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3392905649810), (.variance 142344991624)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1922515249552), (.variance 165174311800)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 786474820168), (.variance 208732916643)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 25927982191), (.variance 510085628378)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨117423580139, 120689819475, (.direct 331294831298 312032815873), (.variance 265902210734)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨117423580139, 120689819475, (.direct 151782739331 140353400716), (.variance 327778958972)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨117423580139, 120689819475, (.direct 82716570280 74797510628), (.variance 386506381610)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 25927982191), (.variance 510085628378)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨117423580139, 120689819475, (.direct 54287234842 48037272075), (.chord (.midpoint ⟨368082883373, 192121878114, 228942146251, 312957272022, 240838468973, 151031231662⟩) 43500686443 91625974997)⟩))
                  (.cut 2 (13/32)
                    (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 25927982191), (.chord (.midpoint ⟨423073946291, 151720758346, 208049213680, 334943932462, 220741615894, 224036574273⟩) 43500686443 65931360876)⟩))
                    (.covered))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨117423580139, 120689819475, (.direct 331294831298 312032815873), (.variance 265902210734)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨117423580139, 120689819475, (.direct 151782739331 140353400716), (.variance 327778958972)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨117423580139, 120689819475, (.direct 82716570280 74797510628), (.variance 386506381610)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop2H2NegRestPart0_ok : CutTop2H2NegRestPart0Tree.geometryOK CutTop2H2NegPowerCache CutTop2H2NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
