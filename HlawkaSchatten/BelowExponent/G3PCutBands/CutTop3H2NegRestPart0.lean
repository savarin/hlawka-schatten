/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H2NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H2NegRestPart0Box : Box := (((⟨![9/68, 9/50, 0, -8], ![27/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop3H2NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3384943227667), (.variance 142432595090)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 784153967430), (.variance 208894510676)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 5138384621371), (.variance 127685459253)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3384943227667), (.variance 142432595090)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1917673059572), (.variance 165283422520)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 784153967430), (.variance 208894510676)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 5138384621371), (.variance 127685459253)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3384943227667), (.variance 142432595090)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1917673059572), (.variance 165283422520)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 784153967430), (.variance 208894510676)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 25653894650), (.variance 511507113217)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 310864272858), (.variance 266163581010)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨120689819474, 123862991200, (.direct 151782739331 139662565510), (.variance 328202750909)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨120689819474, 123862991200, (.direct 82716570280 74320989809), (.variance 387153778237)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 25653894650), (.variance 511507113217)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 54287234842 47662831320), (.chord (.midpoint ⟨369674288491, 190872488430, 228341675927, 313540965943, 240259238449, 151947870025⟩) 43500686443 91625974997)⟩))
                  (.cut 0 (45/272)
                    (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 26446631784), (.chord (.midpoint ⟨474423789737, 118769617864, 188086272264, 359794974301, 201668103491, 230759184298⟩) 43500686443 91625974997)⟩))
                    (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 25653894650), (.chord (.midpoint ⟨461484556105, 126664334156, 189735568895, 357573124881, 206515382804, 227308749890⟩) 43500686443 91625974997)⟩)))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 310864272858), (.variance 266163581010)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨120689819474, 123862991200, (.direct 151782739331 139662565510), (.variance 328202750909)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨120689819474, 123862991200, (.direct 82716570280 74320989809), (.variance 387153778237)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop3H2NegRestPart0_ok : CutTop3H2NegRestPart0Tree.geometryOK CutTop3H2NegPowerCache CutTop3H2NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
