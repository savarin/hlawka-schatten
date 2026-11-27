/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H5NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H5NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H5NegRestPart1Box : Box := ((((⟨![45/136, 19/100, 0, -8], ![27/68, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutTop4H5NegRestPart1Tree : RatioRemainder :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (0)
        (.original (.row ⟨123862991199, 126950446638, (.direct 0 1953895586), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (1/8)
          (.cut 3 (1/16)
            (.cut 3 (1/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 1131165907 4434166730), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨123862991199, 126950446638, (.direct 3393509060 7590132277), (.variance 855279885393)⟩)))
            (.original (.row ⟨123862991199, 126950446638, (.direct 10180561190 15596541189), (.variance 729968495271)⟩)))
          (.cut 3 (3/16)
            (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 25544267546), (.variance 595288579784)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 37192598870), (.variance 519516735314)⟩)))))
      (.cut 3 (0)
        (.cut 3 (-1/8)
          (.cut 2 (5/16)
            (.cut 2 (7/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 10180561190 4565834898), (.chord .universal 10180665226 24716235638)⟩))
              (.covered))
            (.covered))
          (.covered))
        (.cut 3 (1/8)
          (.cut 2 (5/16)
            (.cut 3 (1/16)
              (.covered)
              (.cut 2 (7/32)
                (.cut 2 (11/64)
                  (.cut 3 (3/32)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 6452795533 11330621414), (.chord (.secant 1357380214130 170183780357 14468329444 107518179366) 10180665226 16864782083)⟩))
                    (.original (.row ⟨123862991199, 126950446638, (.direct 10180561190 15596541189), (.chord (.secant 1549820459497 265329679835 47774821297 166412059821) 10180665226 16864782083)⟩)))
                  (.covered))
                (.covered)))
            (.covered))
          (.cut 2 (5/16)
            (.cut 2 (7/32)
              (.cut 3 (3/16)
                (.cut 2 (11/64)
                  (.cut 3 (5/32)
                    (.cut 2 (19/128)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 14500097491 20345315715), (.chord (.secant 1751516784306 375208170737 138801294146 295567070881) 10180665226 13368036905)⟩))
                      (.original (.row ⟨123862991199, 126950446638, (.direct 14500097491 20345315715), (.chord (.secant 1545353727550 263003602806 93678844825 234284056232) 13368036905 16864782083)⟩)))
                    (.cut 2 (19/128)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 25544267546), (.chord (.secant 1962176952916 498527200861 213649036325 391537968867) 10180665226 13368036905)⟩))
                      (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 25544267546), (.chord (.secant 1714425878210 354340964127 150051785299 310356457129) 13368036905 16864782083)⟩))))
                  (.cut 3 (5/32)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 14500097491 20345315715), (.chord (.secant 1401482691395 191002811009 43678156782 159860301103) 16864782083 24716235638)⟩))
                    (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 25544267546), (.chord (.secant 1542108184726 261316662922 77862132489 211767271567) 16864782083 24716235638)⟩))))
                (.cut 2 (11/64)
                  (.cut 2 (19/128)
                    (.cut 3 (7/32)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 24716051037 31167229737), (.chord (.secant 2181537994837 634315720893 299770793619 497114564376) 10180665226 13368036905)⟩))
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 37192598870), (.chord (.secant 2409361529128 781807368407 396199769407 611711664096) 10180665226 13368036905)⟩)))
                    (.cut 3 (7/32)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 24716051037 31167229737), (.chord (.secant 1889889917985 455349026551 215653151278 394042793431) 13368036905 16864782083)⟩))
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 37192598870), (.chord (.secant 2071584676860 565409522553 289636616343 484879321928) 13368036905 16864782083)⟩))))
                  (.cut 3 (7/32)
                    (.cut 2 (25/128)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 24716051037 31167229737), (.chord (.secant 1687635130829 339443311467 158816743230 321773675756) 16864782083 20652546629)⟩))
                      (.original (.row ⟨123862991199, 126950446638, (.direct 24716051037 31167229737), (.chord (.secant 1539643256836 260037269932 118820479351 268869640365) 20652546629 24716235638)⟩)))
                    (.cut 2 (25/128)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 37192598870), (.chord (.secant 1837949058254 424862337405 217180892611 395950400098) 16864782083 20652546629)⟩))
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 37192598870), (.chord (.secant 1667378496960 328279791294 165831511534 330850709654) 20652546629 24716235638)⟩))))))
              (.cut 3 (3/16)
                (.cut 2 (17/64)
                  (.cut 3 (5/32)
                    (.covered)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 25544267546), (.chord (.secant 1319214478418 152702675564 41100252887 155672891765) 24716235638 33622326476)⟩)))
                  (.covered))
                (.cut 2 (17/64)
                  (.cut 3 (7/32)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 24716051037 31167229737), (.chord (.secant 1426917076578 203293233770 68213742077 197649590108) 24716235638 33622326476)⟩))
                    (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 37192598870), (.chord (.secant 1537707548900 259033659267 100079055976 243212824770) 24716235638 33622326476)⟩)))
                  (.cut 3 (7/32)
                    (.covered)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 37192598870), (.chord (.secant 1354154101014 168686374003 61744073238 187982653499) 33622326476 43500686443)⟩))))))
            (.covered)))))
    (.covered)

set_option maxRecDepth 16000 in
theorem CutTop4H5NegRestPart1_ok : CutTop4H5NegRestPart1Tree.geometryOK CutTop4H5NegPowerCache CutTop4H5NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
