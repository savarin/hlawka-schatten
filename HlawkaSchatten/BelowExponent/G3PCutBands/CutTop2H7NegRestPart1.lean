/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H7NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H7NegRestPart1Box : Box := ((((⟨![63/136, 17/100, 0, -8], ![9/17, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutTop2H7NegRestPart1Tree : RatioRemainder :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (0)
        (.cut 3 (-1/8)
          (.original (.row ⟨117423580139, 120689819475, (.direct 10180561190 3708159441), (.variance 848813725125)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 0 2563271455), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (1/8)
          (.cut 3 (1/16)
            (.cut 3 (1/32)
              (.original (.row ⟨117423580139, 120689819475, (.direct 1131165907 5216153935), (.variance 1014295304428)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 3393509060 8504383637), (.variance 814810661529)⟩)))
            (.original (.row ⟨117423580139, 120689819475, (.direct 10180561190 16700147583), (.variance 706519314882)⟩)))
          (.cut 3 (3/16)
            (.original (.row ⟨117423580139, 120689819475, (.direct 19358451269 26768755827), (.variance 584110430723)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 38487961339), (.variance 512922167230)⟩)))))
      (.cut 3 (0)
        (.cut 3 (-1/8)
          (.cut 2 (5/16)
            (.cut 2 (7/32)
              (.cut 3 (-3/16)
                (.original (.row ⟨117423580139, 120689819475, (.direct 19358451269 10222418736), (.variance 650864631859)⟩))
                (.original (.row ⟨117423580139, 120689819475, (.direct 10180561190 3708159441), (.chord (.midpoint ⟨383895725688, 179926476735, 190393415649, 356696093000, 235079109785, 155928439485⟩) 10180665226 24716235638)⟩)))
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
                    (.original (.row ⟨117423580139, 120689819475, (.direct 6452795533 12349894766), (.chord (.secant 1300798042668 144455795739 3965055285 121796140271) 10180665226 16864782083)⟩))
                    (.original (.row ⟨117423580139, 120689819475, (.direct 10180561190 16700147583), (.chord (.secant 1488688312594 233948458443 29186847969 182529521140) 10180665226 16864782083)⟩)))
                  (.covered))
                (.covered)))
            (.covered))
          (.cut 2 (5/16)
            (.cut 3 (3/16)
              (.cut 2 (7/32)
                (.cut 2 (11/64)
                  (.cut 3 (5/32)
                    (.cut 2 (19/128)
                      (.original (.row ⟨117423580139, 120689819475, (.direct 14500097491 21516468028), (.chord (.secant 1685772207474 338412983471 111635262016 317756902774) 10180665226 13368036905)⟩))
                      (.original (.row ⟨117423580139, 120689819475, (.direct 14500097491 21516468028), (.chord (.secant 1475493402888 227307922669 68701419308 251873094540) 13368036905 16864782083)⟩)))
                    (.cut 2 (19/128)
                      (.original (.row ⟨117423580139, 120689819475, (.direct 19358451269 26768755827), (.chord (.secant 1891754816251 456452209954 180836800912 415214279490) 10180665226 13368036905)⟩))
                      (.original (.row ⟨117423580139, 120689819475, (.direct 19358451269 26768755827), (.chord (.secant 1640335482480 313515627492 119408218379 329123719737) 13368036905 16864782083)⟩))))
                  (.cut 3 (5/32)
                    (.original (.row ⟨117423580139, 120689819475, (.direct 14500097491 21516468028), (.chord (.secant 1329151171782 157204130070 23897175629 171861924283) 16864782083 24716235638)⟩))
                    (.original (.row ⟨117423580139, 120689819475, (.direct 19358451269 26768755827), (.chord (.secant 1465924362956 222522905522 52262394937 224572884577) 16864782083 24716235638)⟩))))
                (.cut 2 (17/64)
                  (.cut 3 (5/32)
                    (.covered)
                    (.original (.row ⟨117423580139, 120689819475, (.direct 19358451269 26768755827), (.chord (.secant 1241015476677 118593640537 20686647842 165086465417) 24716235638 33622326476)⟩)))
                  (.covered)))
              (.cut 2 (7/32)
                (.cut 2 (11/64)
                  (.cut 3 (7/32)
                    (.cut 2 (19/128)
                      (.original (.row ⟨117423580139, 120689819475, (.direct 24716051037 32432668716), (.chord (.secant 2106371200828 587034738018 261620855884 521967779839) 10180665226 13368036905)⟩))
                      (.original (.row ⟨117423580139, 120689819475, (.direct 24716051037 32432668716), (.chord (.secant 1811532846381 409539600628 179754651468 413742941342) 13368036905 16864782083)⟩)))
                    (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 38487961339), (.variance 486762498609)⟩)))
                  (.cut 3 (7/32)
                    (.original (.row ⟨117423580139, 120689819475, (.direct 24716051037 32432668716), (.chord (.secant 1607579224081 295853131349 88041241392 282311782678) 16864782083 24716235638)⟩))
                    (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 38487961339), (.chord (.secant 1753999161502 376614512656 130262778831 344784623390) 16864782083 24716235638)⟩))))
                (.cut 2 (17/64)
                  (.cut 3 (7/32)
                    (.original (.row ⟨117423580139, 120689819475, (.direct 24716051037 32432668716), (.chord (.secant 1345454062439 164666132082 42533982252 207531101949) 24716235638 33622326476)⟩))
                    (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 38487961339), (.chord (.secant 1452974601570 216089259700 69682755469 253455865352) 24716235638 33622326476)⟩)))
                  (.cut 3 (7/32)
                    (.covered)
                    (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 38487961339), (.chord (.secant 1269551914926 130759814645 36173708736 195899645337) 33622326476 43500686443)⟩))))))
            (.covered)))))
    (.covered)

set_option maxRecDepth 16000 in
theorem CutTop2H7NegRestPart1_ok : CutTop2H7NegRestPart1Tree.geometryOK CutTop2H7NegPowerCache CutTop2H7NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
