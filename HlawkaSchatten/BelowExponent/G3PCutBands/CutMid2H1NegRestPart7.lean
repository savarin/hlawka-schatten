/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1NegRestPart7`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1NegRestPart7Box : Box := (((((((((⟨![9/68, 9/100, 0, -8], ![9/34, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutMid2H1NegRestPart7Tree : RatioRemainder :=
  .cut 1 (1/10)
    (.cut 3 (3/32)
      (.cut 2 (1/16)
        (.original (.row ⟨86531900008, 91020629598, (.direct 6452795533 7883555910), (.variance 837096923266)⟩))
        (.cut 2 (3/32)
          (.original (.row ⟨86531900008, 91020629598, (.direct 6452795533 7883555910), (.chord (.secant 2065547704967 561673703845 81482976697 166570312026) 3393555298 6452870597)⟩))
          (.original (.row ⟨86531900008, 91020629598, (.direct 6452795533 7883555910), (.chord (.secant 1569979561170 275890214065 36980387308 105578086049) 6452870597 10180665226)⟩))))
      (.cut 0 (27/136)
        (.cut 1 (19/200)
          (.cut 3 (7/64)
            (.original (.row ⟨86531900008, 88806993133, (.direct 8238656156 9316012531), (.variance 716570326964)⟩))
            (.original (.row ⟨86531900008, 88806993133, (.direct 10180561190 11321390084), (.variance 674677497073)⟩)))
          (.cut 3 (7/64)
            (.cut 2 (1/16)
              (.original (.row ⟨88806993132, 91020629598, (.direct 8238656156 9377114392), (.variance 715586344051)⟩))
              (.original (.row ⟨88806993132, 91020629598, (.direct 8238656156 9377114392), (.chord (.secant 2249006764037 677365164906 122106936473 192171933158) 3393555298 10180665226)⟩)))
            (.original (.row ⟨88806993132, 91020629598, (.direct 10180561190 11385888331), (.variance 673889748574)⟩))))
        (.cut 1 (19/200)
          (.original (.row ⟨86531900008, 88806993133, (.direct 10180561190 11711489848), (.variance 708281613509)⟩))
          (.original (.row ⟨88806993132, 91020629598, (.direct 10180561190 11798597318), (.variance 706864560889)⟩)))))
    (.cut 3 (3/32)
      (.cut 2 (1/16)
        (.original (.row ⟨91020629597, 95281442641, (.direct 6452795533 8041068148), (.variance 833645225919)⟩))
        (.cut 2 (3/32)
          (.original (.row ⟨91020629597, 95281442641, (.direct 6452795533 8041068148), (.chord (.secant 2085187381682 573845846862 83521079073 169219515386) 3393555298 6452870597)⟩))
          (.original (.row ⟨91020629597, 95281442641, (.direct 6452795533 8041068148), (.chord (.secant 1581807637300 282133334583 38123593270 107257243739) 6452870597 10180665226)⟩))))
      (.cut 0 (27/136)
        (.cut 1 (21/200)
          (.cut 3 (7/64)
            (.cut 2 (1/16)
              (.original (.row ⟨91020629597, 93177423805, (.direct 8238656156 9438687156), (.variance 714601810113)⟩))
              (.original (.row ⟨91020629597, 93177423805, (.direct 8238656156 9438687156), (.chord (.secant 2256447394686 682146602689 122964137814 193184987216) 3393555298 10180665226)⟩)))
            (.original (.row ⟨91020629597, 93177423805, (.direct 10180561190 11450863139), (.variance 673101005808)⟩)))
          (.cut 3 (7/64)
            (.cut 2 (1/16)
              (.original (.row ⟨93177423804, 95281442641, (.direct 8238656156 9500735484), (.variance 713616720199)⟩))
              (.original (.row ⟨93177423804, 95281442641, (.direct 8238656156 9500735484), (.chord (.secant 2263936532219 686965839167 123828091313 194205367250) 3393555298 10180665226)⟩)))
            (.original (.row ⟨93177423804, 95281442641, (.direct 10180561190 11516319167), (.variance 672311264287)⟩))))
        (.cut 1 (21/200)
          (.cut 3 (7/64)
            (.original (.row ⟨91020629597, 93177423805, (.direct 8238656156 9851913840), (.variance 705449745613)⟩))
            (.original (.row ⟨91020629597, 93177423805, (.direct 10180561190 11886404344), (.variance 665742581437)⟩)))
          (.cut 3 (7/64)
            (.original (.row ⟨93177423804, 95281442641, (.direct 8238656156 9935993921), (.variance 704037148771)⟩))
            (.original (.row ⟨93177423804, 95281442641, (.direct 10180561190 11974917917), (.variance 664602593704)⟩))))))

set_option maxRecDepth 16000 in
theorem CutMid2H1NegRestPart7_ok : CutMid2H1NegRestPart7Tree.geometryOK CutMid2H1NegPowerCache CutMid2H1NegRestPart7Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
