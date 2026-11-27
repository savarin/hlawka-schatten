/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H2NegRestPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H2NegRestPart3Box : Box := ((((((⟨![9/34, 7/100, 0, -8], ![27/68, 9/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid1H2NegRestPart3Tree : RatioRemainder :=
  .cut 2 (5/16)
    (.cut 2 (7/32)
      (.cut 3 (0)
        (.cut 1 (2/25)
          (.cut 1 (3/40)
            (.cut 3 (-1/8)
              (.original (.row ⟨76698504228, 79281022314, (.direct 10180561190 8027419479), (.variance 693394019446)⟩))
              (.covered))
            (.cut 3 (-1/8)
              (.original (.row ⟨79281022313, 81775466253, (.direct 10180561190 7884976506), (.variance 696652491955)⟩))
              (.covered)))
          (.cut 3 (-1/8)
            (.cut 2 (11/64)
              (.original (.row ⟨81775466252, 86531900009, (.direct 10180561190 7600725348), (.variance 703382633359)⟩))
              (.original (.row ⟨81775466252, 86531900009, (.direct 10180561190 7600725348), (.chord (.midpoint ⟨396525368313, 170528183576, 205375192051, 338032314580, 230470348417, 115939405651⟩) 16864782083 24716235638)⟩)))
            (.covered)))
        (.cut 3 (1/8)
          (.cut 1 (2/25)
            (.cut 3 (1/16)
              (.covered)
              (.cut 2 (11/64)
                (.cut 3 (3/32)
                  (.covered)
                  (.original (.row ⟨76698504228, 81775466253, (.direct 10180561190 12111674393), (.chord (.secant 1446506564996 212894155036 21276968548 121060077069) 10180665226 16864782083)⟩)))
                (.covered)))
            (.cut 3 (1/16)
              (.covered)
              (.cut 2 (11/64)
                (.cut 3 (3/32)
                  (.covered)
                  (.original (.row ⟨81775466252, 86531900009, (.direct 10180561190 12373493068), (.chord (.secant 1458714731190 218935048512 22567486964 123493900706) 10180665226 16864782083)⟩)))
                (.covered))))
          (.cut 0 (45/136)
            (.cut 1 (2/25)
              (.original (.row ⟨76698504228, 81775466253, (.direct 30541785600 32568242951), (.variance 634208692228)⟩))
              (.cut 0 (81/272)
                (.cut 3 (3/16)
                  (.cut 3 (5/32)
                    (.original (.row ⟨81775466252, 86531900009, (.direct 14500097491 16279887980), (.chord (.secant 1634855200887 310543518481 44665141710 127386932642) 10180665226 24716235638)⟩))
                    (.original (.row ⟨81775466252, 86531900009, (.direct 19358451269 21257212325), (.variance 579838412099)⟩)))
                  (.original (.row ⟨81775466252, 86531900009, (.direct 30541785600 32604746176), (.variance 540077835106)⟩)))
                (.cut 3 (3/16)
                  (.cut 2 (11/64)
                    (.original (.row ⟨81775466252, 86531900009, (.direct 19358451269 21472194100), (.chord (.secant 1826869217436 418420159994 80161011179 189350483711) 10180665226 16864782083)⟩))
                    (.original (.row ⟨81775466252, 86531900009, (.direct 19358451269 21472194100), (.chord (.secant 1459165024386 219158696154 38679833593 129200534713) 16864782083 24716235638)⟩)))
                  (.original (.row ⟨81775466252, 86531900009, (.direct 30541785600 32837001267), (.variance 538804904288)⟩)))))
            (.cut 1 (2/25)
              (.original (.row ⟨76698504228, 81775466253, (.direct 30541785600 32979234251), (.variance 630110326847)⟩))
              (.cut 0 (99/272)
                (.cut 3 (3/16)
                  (.original (.row ⟨81775466252, 86531900009, (.direct 19358451269 21687973221), (.variance 627118819395)⟩))
                  (.original (.row ⟨81775466252, 86531900009, (.direct 30541785600 33069864231), (.variance 537542144738)⟩)))
                (.cut 3 (3/16)
                  (.original (.row ⟨81775466252, 86531900009, (.direct 19358451269 21904547605), (.variance 624842189648)⟩))
                  (.original (.row ⟨81775466252, 86531900009, (.direct 30541785600 33303333944), (.variance 536289418529)⟩))))))))
      (.cut 3 (0)
        (.cut 1 (2/25)
          (.cut 3 (-1/8)
            (.original (.row ⟨76698504228, 81775466253, (.direct 10180561190 7884976506), (.chord (.midpoint ⟨465814133744, 123992818749, 177351645942, 375113901214, 204897003037, 186435892151⟩) 24716235638 43500686443)⟩))
            (.covered))
          (.cut 3 (-1/8)
            (.original (.row ⟨81775466252, 86531900009, (.direct 10180561190 7600725348), (.chord (.midpoint ⟨469947140338, 121470695630, 175635165038, 377711283159, 203348808369, 188159253881⟩) 24716235638 43500686443)⟩))
            (.covered)))
        (.cut 3 (1/8)
          (.covered)
          (.cut 3 (3/16)
            (.covered)
            (.original (.row ⟨76698504228, 86531900009, (.direct 30541785600 33303333944), (.chord (.secant 1520522879706 250166623622 26375337962 130489141151) 24716235638 43500686443)⟩))))))
    (.covered)

set_option maxRecDepth 16000 in
theorem CutMid1H2NegRestPart3_ok : CutMid1H2NegRestPart3Tree.geometryOK CutMid1H2NegPowerCache CutMid1H2NegRestPart3Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
