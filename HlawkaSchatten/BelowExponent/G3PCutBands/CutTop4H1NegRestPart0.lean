/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H1NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H1NegRestPart0Box : Box := (((⟨![9/136, 19/100, 0, -8], ![9/68, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop4H1NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3425537837915), (.variance 141988660068)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 795991698633), (.variance 208076522951)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 5197574083233), (.variance 127303091982)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3425537837915), (.variance 141988660068)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1942363069158), (.variance 164730671090)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 795991698633), (.variance 208076522951)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 5197574083233), (.variance 127303091982)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3425537837915), (.variance 141988660068)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1942363069158), (.variance 164730671090)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 795991698633), (.variance 208076522951)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 27059936554), (.variance 504409762149)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 316828103755), (.variance 264842431221)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 143191470298), (.variance 326065169574)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 76757794156), (.variance 383896884052)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 27059936554), (.variance 504409762149)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨123862991199, 126950446638, (.direct 54287234842 49579675283), (.chord (.midpoint ⟨394018999044, 172369630415, 225317545982, 316520968403, 231385759274, 160896357784⟩) 43500686443 91625974997)⟩))
                  (.cut 0 (27/272)
                    (.cut 2 (13/32)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 27915833319), (.chord (.midpoint ⟨443531833684, 138068089166, 206751207428, 336434546463, 213191599690, 237864184129⟩) 43500686443 65931360876)⟩))
                      (.covered))
                    (.cut 2 (13/32)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 27059936554), (.chord (.midpoint ⟨432265788765, 145498274948, 207779041772, 335252882366, 217356104865, 234645357916⟩) 43500686443 65931360876)⟩))
                      (.covered)))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 316828103755), (.variance 264842431221)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 143191470298), (.variance 326065169574)⟩))
          (.cut 3 (-15/32)
            (.cut 0 (27/272)
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 78232125737), (.variance 381989068034)⟩))
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 76757794156), (.variance 383896884052)⟩)))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop4H1NegRestPart0_ok : CutTop4H1NegRestPart0Tree.ok CutTop4H1NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
