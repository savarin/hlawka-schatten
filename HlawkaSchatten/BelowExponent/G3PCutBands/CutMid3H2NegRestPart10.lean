/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2NegRestPart10`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H2NegRestPart10Box : Box := (((((((((⟨![9/34, 11/100, 0, -8], ![27/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutMid3H2NegRestPart10Tree : RatioRemainder :=
  .cut 1 (3/25)
    (.cut 3 (3/32)
      (.cut 0 (45/136)
        (.cut 1 (23/200)
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨95281442640, 97336292160, (.direct 4833349683 6781467598), (.variance 796931284745)⟩))
              (.original (.row ⟨95281442640, 97336292160, (.direct 4833349683 6781467598), (.chord (.secant 1808929377430 408036310106 37521233902 127386932642) 3393555298 10180665226)⟩)))
            (.original (.row ⟨95281442640, 97336292160, (.direct 6452795533 8559657062), (.variance 738866925992)⟩)))
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨97336292159, 99345187400, (.direct 4833349683 6877355895), (.variance 793955997351)⟩))
              (.original (.row ⟨97336292159, 99345187400, (.direct 4833349683 6877355895), (.chord (.secant 1820971244032 414999878197 38692048870 129219598187) 3393555298 10180665226)⟩)))
            (.original (.row ⟨97336292159, 99345187400, (.direct 6452795533 8662339570), (.variance 736603778708)⟩))))
        (.cut 1 (23/200)
          (.cut 3 (5/64)
            (.original (.row ⟨95281442640, 97336292160, (.direct 4833349683 7199642966), (.variance 781906084404)⟩))
            (.original (.row ⟨95281442640, 97336292160, (.direct 6452795533 9006891075), (.variance 727385063656)⟩)))
          (.cut 3 (5/64)
            (.original (.row ⟨97336292159, 99345187400, (.direct 4833349683 7317325721), (.variance 778424948936)⟩))
            (.original (.row ⟨97336292159, 99345187400, (.direct 6452795533 9132492840), (.variance 724706071119)⟩)))))
      (.cut 0 (45/136)
        (.cut 1 (23/200)
          (.original (.row ⟨95281442640, 97336292160, (.direct 10180561190 12553240312), (.variance 693085631526)⟩))
          (.original (.row ⟨97336292159, 99345187400, (.direct 10180561190 12667370804), (.variance 691295298215)⟩)))
        (.original (.row ⟨95281442640, 99345187400, (.direct 10180561190 13188442030), (.variance 683972265487)⟩))))
    (.cut 3 (3/32)
      (.cut 0 (45/136)
        (.cut 1 (1/8)
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨99345187399, 101311009181, (.direct 4833349683 6974255551), (.variance 791002716972)⟩))
              (.original (.row ⟨99345187399, 101311009181, (.direct 4833349683 6974255551), (.chord (.secant 1833107031706 422044327099 39882421497 131071732501) 3393555298 10180665226)⟩)))
            (.original (.row ⟨99345187399, 101311009181, (.direct 6452795533 8766024539), (.variance 734352241253)⟩)))
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨101311009180, 103236350716, (.direct 4833349683 7072176851), (.variance 788071102879)⟩))
              (.original (.row ⟨101311009180, 103236350716, (.direct 4833349683 7072176851), (.chord (.secant 1845337680521 429170462957 41092508686 132943532762) 3393555298 10180665226)⟩)))
            (.original (.row ⟨101311009180, 103236350716, (.direct 6452795533 8870722237), (.variance 732112174208)⟩))))
        (.cut 1 (1/8)
          (.cut 3 (5/64)
            (.original (.row ⟨99345187399, 101311009181, (.direct 4833349683 7436344456), (.variance 774977992354)⟩))
            (.original (.row ⟨99345187399, 101311009181, (.direct 6452795533 9259410422), (.variance 722046438350)⟩)))
          (.cut 3 (5/64)
            (.original (.row ⟨101311009180, 103236350716, (.direct 4833349683 7556712566), (.variance 771564553008)⟩))
            (.original (.row ⟨101311009180, 103236350716, (.direct 6452795533 9387657214), (.variance 719405870793)⟩)))))
      (.cut 0 (45/136)
        (.cut 1 (1/8)
          (.original (.row ⟨99345187399, 101311009181, (.direct 10180561190 12782493823), (.variance 689511236636)⟩))
          (.original (.row ⟨101311009180, 103236350716, (.direct 10180561190 12898619500), (.variance 687733385415)⟩)))
        (.original (.row ⟨99345187399, 103236350716, (.direct 10180561190 13470259428), (.variance 679709298338)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid3H2NegRestPart10_ok : CutMid3H2NegRestPart10Tree.geometryOK CutMid3H2NegPowerCache CutMid3H2NegRestPart10Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
