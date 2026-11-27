/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H3NegRestPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H3NegRestPart2Box : Box := (((((((((⟨![27/68, 7/100, 0, -8], ![9/17, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).lowerChild 3 (0)).upperChild 1 (2/25)).lowerChild 1 (17/200)

set_option maxRecDepth 16000 in
def CutMid1H3NegRestPart2Tree : RatioRemainder :=
  .cut 3 (-1/8)
    (.original (.row ⟨81775466252, 84190079492, (.direct 10180561190 6985877790), (.variance 719092269317)⟩))
    (.cut 1 (33/400)
      (.cut 0 (63/136)
        (.cut 3 (-1/16)
          (.original (.row ⟨81775466252, 82992286623, (.direct 3393509060 1761441975), (.chord .universal 0 10180665226)⟩))
          (.cut 1 (13/160)
            (.cut 0 (117/272)
              (.cut 2 (1/16)
                (.original (.row ⟨81775466252, 82386310187, (.direct 0 480810562), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨81775466252, 82386310187, (.direct 0 540736285), (.chord .universal 0 3393555298)⟩))
                (.covered)))
            (.cut 0 (117/272)
              (.cut 2 (1/16)
                (.original (.row ⟨82386310186, 82992286623, (.direct 0 493096357), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨82386310186, 82992286623, (.direct 0 554553317), (.chord .universal 0 3393555298)⟩))
                (.covered)))))
        (.cut 3 (-1/16)
          (.original (.row ⟨81775466252, 82992286623, (.direct 3393509060 1561483429), (.variance 1064565424542)⟩))
          (.cut 1 (13/160)
            (.cut 0 (135/272)
              (.cut 2 (1/16)
                (.original (.row ⟨81775466252, 82386310187, (.direct 0 603220504), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 0 (279/544)
                (.cut 2 (1/16)
                  (.original (.row ⟨81775466252, 82386310187, (.direct 0 635399189), (.chord .universal 0 3393555298)⟩))
                  (.covered))
                (.original (.empty))))
            (.cut 0 (135/272)
              (.cut 3 (-1/32)
                (.original (.row ⟨82386310186, 82992286623, (.direct 1131165907 163661772), (.chord .universal 0 10180665226)⟩))
                (.cut 2 (1/16)
                  (.original (.row ⟨82386310186, 82992286623, (.direct 0 618634149), (.chord .universal 0 3393555298)⟩))
                  (.covered)))
              (.cut 0 (279/544)
                (.cut 3 (-1/32)
                  (.original (.row ⟨82386310186, 82992286623, (.direct 1131165907 143514222), (.chord .universal 0 10180665226)⟩))
                  (.cut 2 (1/16)
                    (.original (.row ⟨82386310186, 82992286623, (.direct 0 651635072), (.chord .universal 0 3393555298)⟩))
                    (.covered)))
                (.original (.empty)))))))
      (.cut 0 (63/136)
        (.cut 3 (-1/16)
          (.original (.row ⟨82992286622, 84190079492, (.direct 3393509060 1716379563), (.chord .universal 0 10180665226)⟩))
          (.cut 1 (67/800)
            (.cut 0 (117/272)
              (.cut 2 (1/16)
                (.original (.row ⟨82992286622, 83593507230, (.direct 0 505512434), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨82992286622, 83593507230, (.direct 0 568516869), (.chord .universal 0 3393555298)⟩))
                (.covered)))
            (.cut 0 (117/272)
              (.cut 2 (1/16)
                (.original (.row ⟨83593507229, 84190079492, (.direct 0 518058527), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 3 (-1/32)
                (.original (.row ⟨83593507229, 84190079492, (.direct 1131165907 187232386), (.chord .universal 0 10180665226)⟩))
                (.cut 2 (1/16)
                  (.original (.row ⟨83593507229, 84190079492, (.direct 0 582626641), (.chord .universal 0 3393555298)⟩))
                  (.covered))))))
        (.cut 3 (-1/16)
          (.original (.row ⟨82992286622, 84190079492, (.direct 3393509060 1512278646), (.chord .universal 0 10180665226)⟩))
          (.cut 1 (67/800)
            (.cut 0 (135/272)
              (.cut 3 (-1/32)
                (.original (.row ⟨82992286622, 83593507230, (.direct 1131165907 153981846), (.chord .universal 0 10180665226)⟩))
                (.cut 1 (133/1600)
                  (.cut 2 (1/16)
                    (.original (.row ⟨82992286622, 83293484592, (.direct 0 626402287), (.chord .universal 0 3393555298)⟩))
                    (.covered))
                  (.cut 2 (1/16)
                    (.original (.row ⟨83293484591, 83593507230, (.direct 0 634211245), (.chord .universal 0 3393555298)⟩))
                    (.covered))))
              (.cut 0 (279/544)
                (.cut 3 (-1/32)
                  (.original (.row ⟨82992286622, 83593507230, (.direct 1131165907 133998219), (.chord .universal 0 10180665226)⟩))
                  (.cut 1 (133/1600)
                    (.cut 2 (1/16)
                      (.original (.row ⟨82992286622, 83293484592, (.direct 0 659817599), (.chord .universal 0 3393555298)⟩))
                      (.covered))
                    (.cut 2 (1/16)
                      (.original (.row ⟨83293484591, 83593507230, (.direct 0 668043124), (.chord .universal 0 3393555298)⟩))
                      (.covered))))
                (.original (.empty))))
            (.cut 0 (135/272)
              (.cut 3 (-1/32)
                (.original (.row ⟨83593507229, 84190079492, (.direct 1131165907 144509281), (.chord .universal 0 10180665226)⟩))
                (.cut 1 (27/320)
                  (.cut 0 (261/544)
                    (.cut 2 (1/16)
                      (.original (.row ⟨83593507229, 83892367844, (.direct 0 608471820), (.chord .universal 0 3393555298)⟩))
                      (.covered))
                    (.cut 2 (1/16)
                      (.original (.row ⟨83593507229, 83892367844, (.direct 0 642060981), (.chord .universal 0 3393555298)⟩))
                      (.covered)))
                  (.cut 0 (261/544)
                    (.cut 2 (1/16)
                      (.original (.row ⟨83892367843, 84190079492, (.direct 0 615949509), (.chord .universal 0 3393555298)⟩))
                      (.covered))
                    (.cut 2 (1/16)
                      (.original (.row ⟨83892367843, 84190079492, (.direct 0 649951458), (.chord .universal 0 3393555298)⟩))
                      (.covered)))))
              (.cut 0 (279/544)
                (.cut 3 (-1/32)
                  (.original (.row ⟨83593507229, 84190079492, (.direct 1131165907 124713413), (.chord .universal 0 10180665226)⟩))
                  (.cut 1 (27/320)
                    (.cut 2 (1/16)
                      (.original (.row ⟨83593507229, 83892367844, (.direct 0 676311604), (.chord .universal 0 3393555298)⟩))
                      (.covered))
                    (.cut 2 (1/16)
                      (.original (.row ⟨83892367843, 84190079492, (.direct 0 684622996), (.chord .universal 0 3393555298)⟩))
                      (.covered))))
                (.original (.empty))))))))

set_option maxRecDepth 16000 in
theorem CutMid1H3NegRestPart2_ok : CutMid1H3NegRestPart2Tree.ok CutMid1H3NegRestPart2Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
