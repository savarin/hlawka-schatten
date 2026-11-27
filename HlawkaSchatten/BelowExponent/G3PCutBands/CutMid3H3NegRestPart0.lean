/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3NegRestPart0Box : Box := (((⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid3H3NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3280138297655), (.variance 143610480416)⟩))
          (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 753655136693), (.variance 211075805581)⟩)))
        (.cut 3 (-5)
          (.original (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3280138297655), (.variance 143610480416)⟩))
          (.cut 3 (-7/2)
            (.original (.row ⟨95281442640, 103236350716, (.direct 2002014560937 1853967227737), (.variance 166752125456)⟩))
            (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 753655136693), (.variance 211075805581)⟩)))))
      (.cut 3 (-5)
        (.original (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3280138297655), (.variance 143610480416)⟩))
        (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 753655136693), (.variance 211075805581)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 22126494882), (.variance 531708638969)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨95281442640, 103236350716, (.direct 331294831298 295540869326), (.variance 269710104979)⟩))
          (.cut 0 (63/136)
            (.cut 3 (-11/16)
              (.original (.row ⟨95281442640, 103236350716, (.direct 151782739331 133211709684), (.variance 332292231098)⟩))
              (.cut 0 (117/272)
                (.cut 3 (-15/32)
                  (.original (.row ⟨95281442640, 103236350716, (.direct 82716570280 70774070084), (.variance 392143206670)⟩))
                  (.cut 1 (3/25)
                    (.original (.row ⟨95281442640, 99345187400, (.direct 30541785600 24168670048), (.variance 519557939613)⟩))
                    (.original (.row ⟨99345187399, 103236350716, (.direct 30541785600 23627652879), (.variance 522647207163)⟩))))
                (.cut 3 (-15/32)
                  (.original (.row ⟨95281442640, 103236350716, (.direct 82716570280 69884071788), (.variance 393444853133)⟩))
                  (.cut 1 (3/25)
                    (.original (.row ⟨95281442640, 99345187400, (.direct 30541785600 23701463321), (.variance 522220510229)⟩))
                    (.original (.row ⟨99345187399, 103236350716, (.direct 30541785600 23123230283), (.variance 525609011263)⟩))))))
            (.cut 3 (-11/16)
              (.original (.row ⟨95281442640, 103236350716, (.direct 151782739331 130632204207), (.variance 333998055077)⟩))
              (.cut 0 (135/272)
                (.cut 3 (-15/32)
                  (.original (.row ⟨95281442640, 103236350716, (.direct 82716570280 68998237184), (.variance 394761349054)⟩))
                  (.cut 2 (5/16)
                    (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 22622836568), (.variance 528628832907)⟩))
                    (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 22622836568), (.chord (.midpoint ⟨330373269025, 223242616465, 212755343571, 329670158730, 254559592075, 83481618059⟩) 43500686443 91625974997)⟩))))
                (.cut 1 (3/25)
                  (.original (.row ⟨95281442640, 99345187400, (.direct 30541785600 22777191081), (.variance 527688400450)⟩))
                  (.cut 3 (-15/32)
                    (.original (.row ⟨99345187399, 103236350716, (.direct 82716570280 68116580205), (.variance 396092985908)⟩))
                    (.original (.row ⟨99345187399, 103236350716, (.direct 30541785600 22126494882), (.variance 531708638969)⟩)))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨95281442640, 103236350716, (.direct 331294831298 295540869326), (.variance 269710104979)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨95281442640, 103236350716, (.direct 151782739331 130632204207), (.variance 333998055077)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨95281442640, 103236350716, (.direct 82716570280 68116580205), (.variance 396092985908)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutMid3H3NegRestPart0_ok : CutMid3H3NegRestPart0Tree.geometryOK CutMid3H3NegPowerCache CutMid3H3NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
