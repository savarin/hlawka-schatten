/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H6NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H6NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H6NegRestPart0Box : Box := (((⟨![27/68, 9/50, 0, -8], ![63/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop3H6NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4873417665484), (.variance 129467953751)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3203306558382), (.variance 144504571388)⟩)))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 731356754041), (.variance 212742344158)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4873417665484), (.variance 129467953751)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3203306558382), (.variance 144504571388)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1807300549809), (.variance 167869021275)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 731356754041), (.variance 212742344158)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 4873417665484), (.variance 129467953751)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3203306558382), (.variance 144504571388)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1807300549809), (.variance 167869021275)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 731356754041), (.variance 212742344158)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 19640228804), (.variance 548566345757)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 284377627551), (.variance 272443217095)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨120689819474, 123862991200, (.direct 151782739331 124088951440), (.variance 338522777001)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨120689819474, 123862991200, (.direct 82716570280 63651474217), (.variance 403187855506)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 19640228804), (.variance 548566345757)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 54287234842 39335586627), (.chord (.midpoint ⟨282055190062, 267769133415, 238598005020, 303917465723, 272232545584, 113765781052⟩) 43500686443 91625974997)⟩))
                  (.covered)))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 284377627551), (.variance 272443217095)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨120689819474, 123862991200, (.direct 151782739331 124088951440), (.variance 338522777001)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨120689819474, 123862991200, (.direct 82716570280 63651474217), (.variance 403187855506)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop3H6NegRestPart0_ok : CutTop3H6NegRestPart0Tree.geometryOK CutTop3H6NegPowerCache CutTop3H6NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
