/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H6PosPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H6PosRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H6PosRestBox : Box := ⟨![27/68, 4/25, 0, -8], ![63/136, 17/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop1H6PosRestTree : RatioRemainder :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (-5)
              (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3239576536155), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 741876661933), (.variance 211948231976)⟩)))
            (.cut 3 (-5)
              (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3239576536155), (.variance 144079163886)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 741876661933), (.variance 211948231976)⟩))))
          (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 741876661933), (.variance 211948231976)⟩)))
        (.cut 2 (1/2)
          (.original (.row ⟨114055813619, 117423580140, (.direct 30541785600 20803000397), (.variance 540366050785)⟩))
          (.original (.row ⟨114055813619, 117423580140, (.direct 30541785600 20803000397), (.chord .universal 91625974997 274877906944)⟩))))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (0)
              (.original (.row ⟨114055813619, 117423580140, (.direct 0 1878293089), (.chord .universal 0 10180665226)⟩))
              (.cut 3 (1/8)
                (.original (.row ⟨114055813619, 117423580140, (.direct 10180561190 15453355456), (.chord .universal 0 10180665226)⟩))
                (.original (.row ⟨114055813619, 117423580140, (.direct 30541785600 37023311985), (.variance 595576315105)⟩))))
            (.cut 2 (5/16)
              (.cut 3 (0)
                (.cut 1 (33/200)
                  (.cut 2 (7/32)
                    (.original (.row ⟨114055813619, 115752966124, (.direct 0 1783759143), (.chord .universal 10180665226 24716235638)⟩))
                    (.covered))
                  (.cut 2 (7/32)
                    (.original (.row ⟨115752966123, 117423580140, (.direct 0 1878293089), (.chord .universal 10180665226 24716235638)⟩))
                    (.covered)))
                (.cut 3 (1/8)
                  (.cut 3 (1/16)
                    (.covered)
                    (.cut 2 (7/32)
                      (.original (.row ⟨114055813619, 117423580140, (.direct 10180561190 15453355456), (.chord (.midpoint ⟨352187188409, 204879785954, 210210110581, 332497333040, 246621648887, 117981254204⟩) 10180665226 24716235638)⟩))
                      (.covered)))
                  (.cut 2 (7/32)
                    (.original (.row ⟨114055813619, 117423580140, (.direct 30541785600 37023311985), (.variance 595576315105)⟩))
                    (.original (.row ⟨114055813619, 117423580140, (.direct 30541785600 37023311985), (.chord (.midpoint ⟨322593641433, 230041698370, 222219243525, 319645817045, 257393916334, 121125356287⟩) 24716235638 43500686443)⟩)))))
              (.covered)))
          (.covered))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (1/2)
              (.original (.row ⟨114055813619, 117423580140, (.direct 91625662891 97953551824), (.variance 469085575611)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 174227225485 178205139281), (.variance 361376753664)⟩)))
            (.cut 3 (1/2)
              (.original (.row ⟨114055813619, 117423580140, (.direct 91625662891 97953551824), (.variance 469085575611)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 174227225485 178205139281), (.variance 361376753664)⟩))))
          (.cut 3 (1/2)
            (.original (.row ⟨114055813619, 117423580140, (.direct 91625662891 97953551824), (.chord (.midpoint ⟨430437511468, 146724367334, 177709152609, 374578321672, 218030318775, 181903982158⟩) 91625974997 274877906944)⟩))
            (.original (.row ⟨114055813619, 117423580140, (.direct 174227225485 178205139281), (.variance 361376753664)⟩))))))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.original (.cone))
            (.original (.row ⟨114055813619, 117423580140, .zero, (.variance 308270156503)⟩)))
          (.original (.row ⟨114055813619, 117423580140, .zero, (.variance 308270156503)⟩)))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.original (.row ⟨114055813619, 117423580140, (.direct 391506126583 386179430844), (.variance 251464699772)⟩))
                  (.original (.row ⟨114055813619, 117423580140, (.direct 439055879922 431420591406), (.variance 244274817975)⟩)))
                (.original (.row ⟨114055813619, 117423580140, (.direct 488587506629 478485077699), (.variance 237740787022)⟩)))
              (.original (.row ⟨114055813619, 117423580140, (.direct 593382169971 577892936838), (.variance 226275239459)⟩)))
            (.cut 3 (13/8)
              (.original (.row ⟨114055813619, 117423580140, (.direct 391506126583 386179430844), (.variance 251464699772)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 593382169971 577892936838), (.variance 226275239459)⟩))))
          (.original (.row ⟨114055813619, 117423580140, (.direct 391506126583 386179430844), (.variance 251464699772)⟩))))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 796691589511), (.variance 208028641641)⟩))
                  (.original (.row ⟨114055813619, 117423580140, (.direct 1082810704946 1040370365974), (.variance 193987904942)⟩)))
                (.original (.row ⟨114055813619, 117423580140, (.direct 1366046989981 1307238926481), (.variance 182728888236)⟩)))
              (.original (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1905372263108), (.variance 165562171007)⟩)))
            (.cut 3 (13/2)
              (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3333265450894), (.variance 143007552069)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 5340438828596 5035574808043), (.variance 128363011058)⟩))))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 796691589511), (.variance 208028641641)⟩))
                  (.original (.row ⟨114055813619, 117423580140, (.direct 1082810704946 1040370365974), (.variance 193987904942)⟩)))
                (.original (.row ⟨114055813619, 117423580140, (.direct 1366046989981 1307238926481), (.variance 182728888236)⟩)))
              (.cut 3 (17/4)
                (.original (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1905372263108), (.variance 165562171007)⟩))
                (.original (.row ⟨114055813619, 117423580140, (.direct 2723407729414 2582754257109), (.variance 152886496395)⟩))))
            (.cut 3 (13/2)
              (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3333265450894), (.variance 143007552069)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 5340438828596 5035574808043), (.variance 128363011058)⟩)))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 796691589511), (.variance 208028641641)⟩))
            (.original (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1905372263108), (.variance 165562171007)⟩)))
          (.cut 3 (13/2)
            (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3333265450894), (.variance 143007552069)⟩))
            (.original (.row ⟨114055813619, 117423580140, (.direct 5340438828596 5035574808043), (.variance 128363011058)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop1H6PosRest_ok : CutTop1H6PosRestTree.geometryOK CutTop1H6PosPowerCache CutTop1H6PosRestBox true (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
