/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H3NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H3NegRestPart0Box : Box := (((⟨![27/136, 17/100, 0, -8], ![9/34, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop2H3NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3349752826757), (.variance 142822901695)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 773903075098), (.variance 209615538506)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5087066484009), (.variance 128021503404)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3349752826757), (.variance 142822901695)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1896276422797), (.variance 165769756447)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 773903075098), (.variance 209615538506)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5087066484009), (.variance 128021503404)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3349752826757), (.variance 142822901695)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1896276422797), (.variance 165769756447)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 773903075098), (.variance 209615538506)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 24452676627), (.variance 517970947799)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨117423580139, 120689819475, (.direct 331294831298 305707120891), (.variance 267332081413)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨117423580139, 120689819475, (.direct 151782739331 136617329258), (.variance 330102884501)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨117423580139, 120689819475, (.direct 82716570280 72223559070), (.variance 390066898415)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 24452676627), (.variance 517970947799)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨117423580139, 120689819475, (.direct 54287234842 46017109681), (.chord (.midpoint ⟨344883456790, 210915411778, 231730002793, 310281218189, 249278546148, 141654847476⟩) 43500686443 91625974997)⟩))
                  (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 24452676627), (.chord (.midpoint ⟨451115896636, 133185934777, 190403049505, 356683287773, 210377680766, 216618070960⟩) 43500686443 91625974997)⟩))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨117423580139, 120689819475, (.direct 331294831298 305707120891), (.variance 267332081413)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨117423580139, 120689819475, (.direct 151782739331 136617329258), (.variance 330102884501)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨117423580139, 120689819475, (.direct 82716570280 72223559070), (.variance 390066898415)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop2H3NegRestPart0_ok : CutTop2H3NegRestPart0Tree.ok CutTop2H3NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
