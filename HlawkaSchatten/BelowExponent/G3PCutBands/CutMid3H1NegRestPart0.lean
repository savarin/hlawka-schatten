/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H1NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H1NegRestPart0Box : Box := (((⟨![9/68, 11/100, 0, -8], ![9/34, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid3H1NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3401056459895), (.variance 142255583784)⟩))
          (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 788851119775), (.variance 208568084278)⟩)))
        (.cut 3 (-5)
          (.original (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3401056459895), (.variance 142255583784)⟩))
          (.cut 3 (-7/2)
            (.original (.row ⟨95281442640, 103236350716, (.direct 2002014560937 1927472322266), (.variance 165062971018)⟩))
            (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 788851119775), (.variance 208568084278)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨95281442640, 103236350716, (.direct 5340438828596 5161879939016), (.variance 127533016165)⟩))
          (.original (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3401056459895), (.variance 142255583784)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨95281442640, 103236350716, (.direct 2002014560937 1927472322266), (.variance 165062971018)⟩))
          (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 788851119775), (.variance 208568084278)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 26209419223), (.variance 508645623743)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨95281442640, 103236350716, (.direct 331294831298 313229631314), (.variance 265635793917)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨95281442640, 103236350716, (.direct 151782739331 141061261854), (.variance 327347444093)⟩))
            (.cut 0 (27/136)
              (.cut 3 (-15/32)
                (.original (.row ⟨95281442640, 103236350716, (.direct 82716570280 77119503490), (.variance 383424569070)⟩))
                (.cut 0 (45/272)
                  (.cut 1 (3/25)
                    (.original (.row ⟨95281442640, 99345187400, (.direct 30541785600 28025803539), (.variance 499798584117)⟩))
                    (.original (.row ⟨99345187399, 103236350716, (.direct 30541785600 27805435960), (.variance 500832809344)⟩)))
                  (.cut 1 (3/25)
                    (.original (.row ⟨95281442640, 99345187400, (.direct 30541785600 27532195904), (.variance 502129630911)⟩))
                    (.original (.row ⟨99345187399, 103236350716, (.direct 30541785600 27269565154), (.variance 503391498620)⟩)))))
              (.cut 3 (-15/32)
                (.original (.row ⟨95281442640, 103236350716, (.direct 82716570280 75286040152), (.variance 385848050675)⟩))
                (.cut 0 (63/272)
                  (.cut 1 (3/25)
                    (.original (.row ⟨95281442640, 99345187400, (.direct 30541785600 27041833005), (.variance 504498166221)⟩))
                    (.original (.row ⟨99345187399, 103236350716, (.direct 30541785600 26737552922), (.variance 505995311651)⟩)))
                  (.cut 1 (3/25)
                    (.original (.row ⟨95281442640, 99345187400, (.direct 30541785600 26554730150), (.variance 506905230847)⟩))
                    (.original (.row ⟨99345187399, 103236350716, (.direct 30541785600 26209419223), (.variance 508645623743)⟩)))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨95281442640, 103236350716, (.direct 331294831298 313229631314), (.variance 265635793917)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨95281442640, 103236350716, (.direct 151782739331 141061261854), (.variance 327347444093)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨95281442640, 103236350716, (.direct 82716570280 75286040152), (.variance 385848050675)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutMid3H1NegRestPart0_ok : CutMid3H1NegRestPart0Tree.ok CutMid3H1NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
