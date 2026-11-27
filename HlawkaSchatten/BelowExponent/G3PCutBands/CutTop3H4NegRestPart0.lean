/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H4NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H4NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H4NegRestPart0Box : Box := (((⟨![9/34, 9/50, 0, -8], ![45/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop3H4NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3293662760743), (.variance 143455831009)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 757585599369), (.variance 210788498917)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 5005254009236), (.variance 128566175514)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3293662760743), (.variance 143455831009)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1862184990233), (.variance 166559118617)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 757585599369), (.variance 210788498917)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 5005254009236), (.variance 128566175514)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3293662760743), (.variance 143455831009)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1862184990233), (.variance 166559118617)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 757585599369), (.variance 210788498917)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 22573083161), (.variance 528933691388)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 297512153685), (.variance 269241001566)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨120689819474, 123862991200, (.direct 151782739331 131790842188), (.variance 333226638445)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨120689819474, 123862991200, (.direct 82716570280 68909995884), (.variance 394893657518)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 22573083161), (.variance 528933691388)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 54287234842 43425506276), (.chord (.midpoint ⟨324773178023, 228123225550, 233509798385, 308601400756, 256599579098, 133828126085⟩) 43500686443 91625974997)⟩))
                  (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 22573083161), (.chord (.midpoint ⟨427911850351, 148427566792, 192833991755, 353487101391, 218961015441, 210361973385⟩) 43500686443 91625974997)⟩))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 297512153685), (.variance 269241001566)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨120689819474, 123862991200, (.direct 151782739331 131790842188), (.variance 333226638445)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨120689819474, 123862991200, (.direct 82716570280 68909995884), (.variance 394893657518)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop3H4NegRestPart0_ok : CutTop3H4NegRestPart0Tree.geometryOK CutTop3H4NegPowerCache CutTop3H4NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
