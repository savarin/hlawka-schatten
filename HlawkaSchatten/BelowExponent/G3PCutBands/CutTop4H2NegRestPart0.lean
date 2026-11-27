/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegRestPart0Box : Box := (((⟨![9/68, 19/100, 0, -8], ![27/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop4H2NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3376899356470), (.variance 142521359100)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 781809902204), (.variance 209058334676)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 5126654938411), (.variance 127761893714)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3376899356470), (.variance 142521359100)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1912781651244), (.variance 165393995835)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 781809902204), (.variance 209058334676)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 5126654938411), (.variance 127761893714)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3376899356470), (.variance 142521359100)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1912781651244), (.variance 165393995835)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 781809902204), (.variance 209058334676)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 25377856249), (.variance 512958217805)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 309684392050), (.variance 266428748128)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 138965334309), (.variance 328633157005)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 73840318100), (.variance 387812142509)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 25377856249), (.variance 512958217805)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨123862991199, 126950446638, (.direct 54287234842 47285330761), (.chord (.midpoint ⟨371285950715, 189612278075, 227733392450, 314134936273, 239672562934, 152870665571⟩) 43500686443 91625974997)⟩))
                  (.cut 0 (45/272)
                    (.cut 2 (13/32)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 26213916696), (.chord (.midpoint ⟨421107086091, 153071224232, 208803281219, 334085249950, 221464749952, 231394893374⟩) 43500686443 65931360876)⟩))
                      (.covered))
                    (.cut 2 (13/32)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 25377856249), (.chord (.midpoint ⟨410056463358, 160785052309, 209823968279, 332931367212, 225520009902, 228111704435⟩) 43500686443 65931360876)⟩))
                      (.covered)))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 309684392050), (.variance 266428748128)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 138965334309), (.variance 328633157005)⟩))
          (.cut 2 (3/4)
            (.cut 3 (-15/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 73840318100), (.chord (.midpoint ⟨409449688728, 161214881698, 213260119922, 329116326915, 225742331130, 177475313329⟩) 91625974997 174227471798)⟩))
              (.covered))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop4H2NegRestPart0_ok : CutTop4H2NegRestPart0Tree.ok CutTop4H2NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
