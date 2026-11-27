/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H2NegRestPart1Box : Box := (((((((⟨![9/34, 11/100, 0, -8], ![27/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).lowerChild 3 (0)

set_option maxRecDepth 16000 in
def CutMid3H2NegRestPart1Tree : RatioRemainder :=
  .cut 1 (3/25)
    (.cut 1 (23/200)
      (.cut 3 (-1/8)
        (.original (.row ⟨95281442640, 97336292160, (.direct 10180561190 6894468453), (.variance 721576710865)⟩))
        (.cut 0 (45/136)
          (.cut 1 (9/80)
            (.cut 3 (-1/16)
              (.original (.row ⟨95281442640, 96314804182, (.direct 3393509060 1776477234), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨95281442640, 96314804182, (.direct 0 545359040), (.chord .universal 0 10180665226)⟩)))
            (.cut 3 (-1/16)
              (.original (.row ⟨96314804181, 97336292160, (.direct 3393509060 1743110895), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨96314804181, 97336292160, (.direct 0 565879290), (.chord .universal 0 10180665226)⟩))))
          (.cut 1 (9/80)
            (.cut 3 (-1/16)
              (.original (.row ⟨95281442640, 96314804182, (.direct 3393509060 1500958557), (.chord .universal 0 10180665226)⟩))
              (.cut 0 (99/272)
                (.original (.row ⟨95281442640, 96314804182, (.direct 0 634290732), (.chord .universal 0 10180665226)⟩))
                (.cut 1 (89/800)
                  (.original (.row ⟨95281442640, 95799632852, (.direct 0 714554035), (.chord .universal 0 10180665226)⟩))
                  (.original (.row ⟨95799632851, 96314804182, (.direct 0 728084548), (.chord .universal 0 10180665226)⟩)))))
            (.cut 3 (-1/16)
              (.original (.row ⟨96314804181, 97336292160, (.direct 3393509060 1463377611), (.chord .universal 0 10180665226)⟩))
              (.cut 0 (99/272)
                (.original (.row ⟨96314804181, 97336292160, (.direct 0 658157219), (.chord .universal 0 10180665226)⟩))
                (.original (.row ⟨96314804181, 97336292160, (.direct 0 755480220), (.chord .universal 0 10180665226)⟩)))))))
      (.cut 3 (-1/8)
        (.original (.row ⟨97336292159, 99345187400, (.direct 10180561190 6754088611), (.variance 725474196799)⟩))
        (.cut 0 (45/136)
          (.cut 1 (47/400)
            (.cut 3 (-1/16)
              (.original (.row ⟨97336292159, 98346296770, (.direct 3393509060 1709890945), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨97336292159, 98346296770, (.direct 0 586733539), (.chord .universal 0 10180665226)⟩)))
            (.cut 3 (-1/16)
              (.original (.row ⟨98346296769, 99345187400, (.direct 3393509060 1676820099), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨98346296769, 99345187400, (.direct 0 607921587), (.chord .universal 0 10180665226)⟩))))
          (.cut 1 (47/400)
            (.cut 3 (-1/16)
              (.original (.row ⟨97336292159, 98346296770, (.direct 3393509060 1426051127), (.chord .universal 0 10180665226)⟩))
              (.cut 0 (99/272)
                (.original (.row ⟨97336292159, 98346296770, (.direct 0 682412171), (.chord .universal 0 10180665226)⟩))
                (.original (.row ⟨97336292159, 98346296770, (.direct 0 783321799), (.chord .universal 0 10180665226)⟩))))
            (.cut 3 (-1/16)
              (.original (.row ⟨98346296769, 99345187400, (.direct 3393509060 1388983956), (.chord .universal 0 10180665226)⟩))
              (.cut 0 (99/272)
                (.original (.row ⟨98346296769, 99345187400, (.direct 0 707055354), (.chord .universal 0 10180665226)⟩))
                (.original (.row ⟨98346296769, 99345187400, (.direct 0 811609017), (.chord .universal 0 10180665226)⟩))))))))
    (.cut 3 (-1/8)
      (.original (.row ⟨99345187399, 103236350716, (.direct 10180561190 6474331913), (.variance 733555200958)⟩))
      (.cut 1 (1/8)
        (.cut 0 (45/136)
          (.cut 3 (-1/16)
            (.original (.row ⟨99345187399, 101311009181, (.direct 3393509060 1611136853), (.chord .universal 0 10180665226)⟩))
            (.cut 1 (49/400)
              (.original (.row ⟨99345187399, 100333314143, (.direct 0 629443292), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨100333314142, 101311009181, (.direct 0 651298572), (.chord .universal 0 10180665226)⟩))))
          (.cut 3 (-1/16)
            (.original (.row ⟨99345187399, 101311009181, (.direct 3393509060 1315647528), (.chord .universal 0 10180665226)⟩))
            (.cut 1 (49/400)
              (.original (.row ⟨99345187399, 100333314143, (.direct 0 840341686), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨100333314142, 101311009181, (.direct 0 869519696), (.chord .universal 0 10180665226)⟩)))))
        (.cut 0 (45/136)
          (.cut 3 (-1/16)
            (.original (.row ⟨101311009180, 103236350716, (.direct 3393509060 1546083981), (.chord .universal 0 10180665226)⟩))
            (.original (.row ⟨101311009180, 103236350716, (.direct 0 696009800), (.chord .universal 0 10180665226)⟩)))
          (.cut 3 (-1/16)
            (.original (.row ⟨101311009180, 103236350716, (.direct 3393509060 1243409536), (.chord .universal 0 10180665226)⟩))
            (.cut 1 (51/400)
              (.original (.row ⟨101311009180, 102278588035, (.direct 0 899143010), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨102278588034, 103236350716, (.direct 0 929211664), (.chord .universal 0 10180665226)⟩)))))))

set_option maxRecDepth 16000 in
theorem CutMid3H2NegRestPart1_ok : CutMid3H2NegRestPart1Tree.geometryOK CutMid3H2NegPowerCache CutMid3H2NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
