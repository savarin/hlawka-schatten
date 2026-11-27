/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H2NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H2NegPart2Box : Box := ((((((((((⟨![9/34, 1/20, 0, -8], ![27/68, 7/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 2 (7/32)).lowerChild 3 (0)).lowerChild 1 (3/50)

set_option maxRecDepth 16000 in
def CutMid0H2NegPart2Tree : CertTree :=
  .cut 1 (11/200)
    (.cut 3 (-1/8)
      (.row ⟨65259754744, 68314662357, (.direct 10180561190 8599000741), (.variance 681016782720)⟩)
      (.cut 2 (11/64)
        (.cut 1 (21/400)
          (.cut 0 (45/136)
            (.row ⟨65259754744, 66806127931, (.direct 0 155070886), (.chord .universal 10180665226 16864782083)⟩)
            (.row ⟨65259754744, 66806127931, (.direct 0 207028228), (.chord .universal 10180665226 16864782083)⟩))
          (.cut 0 (45/136)
            (.row ⟨66806127930, 68314662357, (.direct 0 167276935), (.chord .universal 10180665226 16864782083)⟩)
            (.cut 3 (-1/16)
              (.row ⟨66806127930, 68314662357, (.direct 3393509060 2425850130), (.chord (.midpoint ⟨455292015833, 130538147359, 174454776979, 379522771775, 208824290645, 219969752590⟩) 10180665226 16864782083)⟩)
              (.row ⟨66806127930, 68314662357, (.direct 0 223323981), (.chord .universal 10180665226 16864782083)⟩))))
        (.row ⟨65259754744, 68314662357, (.direct 0 223323981), (.chord .universal 16864782083 24716235638)⟩)))
    (.cut 2 (11/64)
      (.cut 3 (-1/8)
        (.row ⟨68314662356, 71228276419, (.direct 10180561190 8455859207), (.variance 684016904264)⟩)
        (.cut 1 (23/400)
          (.cut 0 (45/136)
            (.row ⟨68314662356, 69787943483, (.direct 0 179853682), (.chord .universal 10180665226 16864782083)⟩)
            (.cut 3 (-1/16)
              (.row ⟨68314662356, 69787943483, (.direct 3393509060 2383539143), (.chord (.midpoint ⟨456998108998, 129464650621, 173732564834, 380641485700, 208188834103, 220709197765⟩) 10180665226 16864782083)⟩)
              (.cut 1 (9/160)
                (.row ⟨68314662356, 69055559459, (.direct 0 231657762), (.chord .universal 10180665226 16864782083)⟩)
                (.cut 0 (99/272)
                  (.row ⟨69055559458, 69787943483, (.direct 0 209182420), (.chord .universal 10180665226 16864782083)⟩)
                  (.row ⟨69055559458, 69787943483, (.direct 0 240114635), (.chord .universal 10180665226 16864782083)⟩)))))
          (.cut 0 (45/136)
            (.cut 3 (-1/16)
              (.row ⟨69787943482, 71228276419, (.direct 3393509060 2506670208), (.chord (.midpoint ⟨487198822408, 111235424794, 168398873344, 389156564459, 196848719059, 230420051769⟩) 10180665226 16864782083)⟩)
              (.row ⟨69787943482, 71228276419, (.direct 0 192797457), (.chord .universal 10180665226 16864782083)⟩))
            (.cut 3 (-1/16)
              (.row ⟨69787943482, 71228276419, (.direct 3393509060 2341395577), (.chord (.midpoint ⟨458710962390, 128391675012, 173006346579, 381774450304, 207550355302, 221448785980⟩) 10180665226 16864782083)⟩)
              (.cut 1 (47/800)
                (.cut 0 (99/272)
                  (.row ⟨69787943482, 70512094189, (.direct 0 216656570), (.chord .universal 10180665226 16864782083)⟩)
                  (.row ⟨69787943482, 70512094189, (.direct 0 248694002), (.chord .universal 10180665226 16864782083)⟩))
                (.cut 2 (19/128)
                  (.cut 0 (99/272)
                    (.row ⟨70512094188, 71228276419, (.direct 0 224236937), (.chord .universal 10180665226 13368036905)⟩)
                    (.row ⟨70512094188, 71228276419, (.direct 0 257395293), (.chord .universal 10180665226 13368036905)⟩))
                  (.cut 3 (-1/32)
                    (.row ⟨70512094188, 71228276419, (.direct 1131165907 496440702), (.chord (.midpoint ⟨556760620741, 74556992996, 128781594352, 470730228831, 169826147327, 313727328714⟩) 13368036905 16864782083)⟩)
                    (.row ⟨70512094188, 71228276419, (.direct 0 257395293), (.chord (.secant 668456878490 30184881996 102910472947 12315950695) 13368036905 16864782083)⟩))))))))
      (.cut 3 (-1/8)
        (.row ⟨68314662356, 71228276419, (.direct 10180561190 8455859207), (.variance 684016904264)⟩)
        (.cut 0 (45/136)
          (.row ⟨68314662356, 71228276419, (.direct 0 192797457), (.chord .universal 16864782083 24716235638)⟩)
          (.cut 1 (23/400)
            (.row ⟨68314662356, 69787943483, (.direct 0 240114635), (.chord .universal 16864782083 24716235638)⟩)
            (.cut 3 (-1/16)
              (.row ⟨69787943482, 71228276419, (.direct 3393509060 2341395577), (.chord (.midpoint ⟨491581542955, 108709364055, 158821399867, 405664827730, 195186901175, 265069892724⟩) 16864782083 24716235638)⟩)
              (.row ⟨69787943482, 71228276419, (.direct 0 257395293), (.chord .universal 16864782083 24716235638)⟩))))))

set_option maxRecDepth 16000 in
theorem CutMid0H2NegPart2_checked : CutMid0H2NegPart2Tree.commonOK CutMid0H2NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
