/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H7NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H7NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H7NegRestPart0Box : Box := (((⟨![63/136, 9/50, 0, -8], ![9/17, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop3H7NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4807987672843), (.variance 129927012378)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3158477161479), (.variance 145038848258)⟩)))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 718370632080), (.variance 213742735163)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4807987672843), (.variance 129927012378)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3158477161479), (.variance 145038848258)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1780086169077), (.variance 168537294628)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 718370632080), (.variance 213742735163)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4807987672843), (.variance 129927012378)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3158477161479), (.variance 145038848258)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1780086169077), (.variance 168537294628)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 718370632080), (.variance 213742735163)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 18230976992), (.variance 559366958062)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 277892766628), (.variance 274093867127)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨120689819474, 123862991200, (.direct 151782739331 120302531304), (.variance 341280985803)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨120689819474, 123862991200, (.direct 82716570280 61080382756), (.variance 407564630295)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 18230976992), (.variance 559366958062)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 54287234842 37347099934), (.chord (.midpoint ⟨261540197025, 288458876761, 241113423236, 301664448609, 279814147354, 102734052093⟩) 43500686443 91625974997)⟩))
                  (.covered)))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 277892766628), (.variance 274093867127)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨120689819474, 123862991200, (.direct 151782739331 120302531304), (.variance 341280985803)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨120689819474, 123862991200, (.direct 82716570280 61080382756), (.chord (.midpoint ⟨342868417993, 212600297612, 207578117980, 335483090551, 250011652980, 122227762773⟩) 91625974997 274877906944)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop3H7NegRestPart0_ok : CutTop3H7NegRestPart0Tree.geometryOK CutTop3H7NegPowerCache CutTop3H7NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
