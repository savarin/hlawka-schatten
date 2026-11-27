/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H5NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H5NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H5NegRestPart0Box : Box := (((⟨![45/136, 9/50, 0, -8], ![27/68, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop3H5NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3248368708090), (.variance 143976945665)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 744428541967), (.variance 211757738889)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4939173491461), (.variance 129014378412)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3248368708090), (.variance 143976945665)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1834667022652), (.variance 167209696807)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 744428541967), (.variance 211757738889)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4939173491461), (.variance 129014378412)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3248368708090), (.variance 143976945665)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1834667022652), (.variance 167209696807)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 744428541967), (.variance 211757738889)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 21087833510), (.variance 538445208770)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 290917532157), (.variance 270825974472)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨120689819474, 123862991200, (.direct 151782739331 127918502385), (.variance 335839119431)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨120689819474, 123862991200, (.direct 82716570280 66261481069), (.variance 398967291759)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 21087833510), (.variance 538445208770)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 54287234842 41361886818), (.chord (.midpoint ⟨303136394220, 247653280470, 236063628794, 306228905160, 264498025704, 124085121044⟩) 43500686443 91625974997)⟩))
                  (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 21087833510), (.chord (.midpoint ⟨403145158465, 165720061831, 196065645365, 349343268525, 228050371313, 202938680800⟩) 43500686443 91625974997)⟩))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 290917532157), (.variance 270825974472)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨120689819474, 123862991200, (.direct 151782739331 127918502385), (.variance 335839119431)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨120689819474, 123862991200, (.direct 82716570280 66261481069), (.variance 398967291759)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop3H5NegRestPart0_ok : CutTop3H5NegRestPart0Tree.geometryOK CutTop3H5NegPowerCache CutTop3H5NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
