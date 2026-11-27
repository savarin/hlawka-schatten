/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1NegPart1Box : Box := (((((((⟨![9/68, 9/100, 0, -8], ![9/34, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).lowerChild 3 (0)

set_option maxRecDepth 16000 in
def CutMid2H1NegPart1Tree : CertTree :=
  .cut 1 (1/10)
    (.cut 1 (19/200)
      (.cut 3 (-1/8)
        (.row ⟨86531900008, 88806993133, (.direct 10180561190 8331388341), (.variance 686678272586)⟩)
        (.cut 0 (27/136)
          (.cut 1 (37/400)
            (.cut 3 (-1/16)
              (.row ⟨86531900008, 87677441236, (.direct 3393509060 2556419282), (.chord .universal 0 10180665226)⟩)
              (.row ⟨86531900008, 87677441236, (.direct 0 175011417), (.chord .universal 0 10180665226)⟩))
            (.cut 3 (-1/16)
              (.row ⟨87677441235, 88806993133, (.direct 3393509060 2533957322), (.chord .universal 0 10180665226)⟩)
              (.row ⟨87677441235, 88806993133, (.direct 0 182947279), (.chord .universal 0 10180665226)⟩)))
          (.cut 1 (37/400)
            (.cut 3 (-1/16)
              (.row ⟨86531900008, 87677441236, (.direct 3393509060 2297206927), (.chord .universal 0 10180665226)⟩)
              (.cut 0 (63/272)
                (.row ⟨86531900008, 87677441236, (.direct 0 223446999), (.chord .universal 0 10180665226)⟩)
                (.cut 1 (73/800)
                  (.row ⟨86531900008, 87106710699, (.direct 0 269943785), (.chord .universal 0 10180665226)⟩)
                  (.row ⟨87106710698, 87677441236, (.direct 0 276114733), (.chord .universal 0 10180665226)⟩))))
            (.cut 3 (-1/16)
              (.row ⟨87677441235, 88806993133, (.direct 3393509060 2268436399), (.chord .universal 0 10180665226)⟩)
              (.cut 0 (63/272)
                (.row ⟨87677441235, 88806993133, (.direct 0 233579164), (.chord .universal 0 10180665226)⟩)
                (.row ⟨87677441235, 88806993133, (.direct 0 288635108), (.chord .universal 0 10180665226)⟩))))))
      (.cut 3 (-1/8)
        (.row ⟨88806993132, 91020629598, (.direct 10180561190 8232971135), (.variance 688818348335)⟩)
        (.cut 0 (27/136)
          (.cut 1 (39/400)
            (.cut 3 (-1/16)
              (.row ⟨88806993132, 89921191063, (.direct 3393509060 2511509865), (.chord .universal 0 10180665226)⟩)
              (.row ⟨88806993132, 89921191063, (.direct 0 191033644), (.chord .universal 0 10180665226)⟩))
            (.cut 3 (-1/16)
              (.row ⟨89921191062, 91020629598, (.direct 3393509060 2489077432), (.chord .universal 0 10180665226)⟩)
              (.row ⟨89921191062, 91020629598, (.direct 0 199270149), (.chord .universal 0 10180665226)⟩)))
          (.cut 1 (39/400)
            (.cut 3 (-1/16)
              (.row ⟨88806993132, 89921191063, (.direct 3393509060 2239724834), (.chord .universal 0 10180665226)⟩)
              (.cut 0 (63/272)
                (.row ⟨88806993132, 89921191063, (.direct 0 243903484), (.chord .universal 0 10180665226)⟩)
                (.row ⟨88806993132, 89921191063, (.direct 0 301392930), (.chord .universal 0 10180665226)⟩)))
            (.cut 3 (-1/16)
              (.row ⟨89921191062, 91020629598, (.direct 3393509060 2211073449), (.chord .universal 0 10180665226)⟩)
              (.cut 0 (63/272)
                (.row ⟨89921191062, 91020629598, (.direct 0 254419498), (.chord .universal 0 10180665226)⟩)
                (.row ⟨89921191062, 91020629598, (.direct 0 314387628), (.chord .universal 0 10180665226)⟩)))))))
    (.cut 1 (21/200)
      (.cut 3 (-1/8)
        (.row ⟨91020629597, 93177423805, (.direct 10180561190 8134470310), (.variance 690992811635)⟩)
        (.cut 0 (27/136)
          (.cut 1 (41/400)
            (.row ⟨91020629597, 92105866080, (.direct 0 207656475), (.chord .universal 0 10180665226)⟩)
            (.row ⟨92105866079, 93177423805, (.direct 0 216192338), (.chord .universal 0 10180665226)⟩))
          (.cut 1 (41/400)
            (.cut 3 (-1/16)
              (.row ⟨91020629597, 92105866080, (.direct 3393509060 2182483480), (.chord .universal 0 10180665226)⟩)
              (.row ⟨91020629597, 92105866080, (.direct 0 327618696), (.chord .universal 0 10180665226)⟩))
            (.cut 3 (-1/16)
              (.row ⟨92105866079, 93177423805, (.direct 3393509060 2153956183), (.chord .universal 0 10180665226)⟩)
              (.row ⟨92105866079, 93177423805, (.direct 0 341085689), (.chord .universal 0 10180665226)⟩)))))
      (.cut 3 (-1/8)
        (.row ⟨93177423804, 95281442641, (.direct 10180561190 8035890059), (.variance 693202551201)⟩)
        (.cut 0 (27/136)
          (.cut 1 (43/400)
            (.row ⟨93177423804, 94235794856, (.direct 0 224877493), (.chord .universal 0 10180665226)⟩)
            (.row ⟨94235794855, 95281442641, (.direct 0 233711729), (.chord .universal 0 10180665226)⟩))
          (.cut 1 (43/400)
            (.cut 3 (-1/16)
              (.row ⟨93177423804, 94235794856, (.direct 3393509060 2125492833), (.chord .universal 0 10180665226)⟩)
              (.row ⟨93177423804, 94235794856, (.direct 0 354788220), (.chord .universal 0 10180665226)⟩))
            (.cut 3 (-1/16)
              (.row ⟨94235794855, 95281442641, (.direct 3393509060 2097094726), (.chord .universal 0 10180665226)⟩)
              (.row ⟨94235794855, 95281442641, (.direct 0 368725954), (.chord .universal 0 10180665226)⟩))))))

set_option maxRecDepth 16000 in
theorem CutMid2H1NegPart1_checked : CutMid2H1NegPart1Tree.commonOK CutMid2H1NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
