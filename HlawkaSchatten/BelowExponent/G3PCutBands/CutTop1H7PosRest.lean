/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop1H7PosPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H7PosRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H7PosRestBox : Box := ⟨![63/136, 4/25, 0, -8], ![9/17, 17/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop1H7PosRestTree : RatioRemainder :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (-5)
              (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3199726618693), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 730319050953), (.variance 212821457326)⟩)))
            (.cut 3 (-5)
              (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3199726618693), (.variance 144546889585)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 730319050953), (.variance 212821457326)⟩))))
          (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 730319050953), (.variance 212821457326)⟩)))
        (.cut 2 (1/2)
          (.original (.row ⟨114055813619, 117423580140, (.direct 30541785600 19526543152), (.variance 549400885193)⟩))
          (.cut 3 (-9/8)
            (.original (.row ⟨114055813619, 117423580140, (.direct 331294831298 283858979914), (.variance 272573478302)⟩))
            (.cut 2 (3/4)
              (.original (.row ⟨114055813619, 117423580140, (.direct 30541785600 19526543152), (.chord .universal 91625974997 174227471798)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 30541785600 19526543152), (.chord .universal 174227471798 274877906944)⟩))))))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (0)
              (.original (.row ⟨114055813619, 117423580140, (.direct 0 2321017507), (.chord .universal 0 10180665226)⟩))
              (.cut 3 (1/8)
                (.original (.row ⟨114055813619, 117423580140, (.direct 10180561190 16271159185), (.variance 1042495520754)⟩))
                (.original (.row ⟨114055813619, 117423580140, (.direct 30541785600 37986365340), (.variance 587736766500)⟩))))
            (.cut 2 (5/16)
              (.cut 3 (0)
                (.cut 1 (33/200)
                  (.cut 1 (13/80)
                    (.cut 3 (-1/8)
                      (.original (.row ⟨114055813619, 114907784327, (.direct 10180561190 4277522644), (.chord .universal 10180665226 43500686443)⟩))
                      (.covered))
                    (.cut 3 (-1/8)
                      (.original (.row ⟨114907784326, 115752966124, (.direct 10180561190 4195033752), (.chord .universal 10180665226 43500686443)⟩))
                      (.covered)))
                  (.cut 1 (67/400)
                    (.cut 3 (-1/8)
                      (.original (.row ⟨115752966123, 116591514757, (.direct 10180561190 4112916569), (.chord .universal 10180665226 43500686443)⟩))
                      (.covered))
                    (.cut 3 (-1/8)
                      (.original (.row ⟨116591514756, 117423580140, (.direct 10180561190 4031178183), (.chord .universal 10180665226 43500686443)⟩))
                      (.covered))))
                (.cut 3 (1/8)
                  (.cut 3 (1/16)
                    (.covered)
                    (.cut 2 (7/32)
                      (.original (.row ⟨114055813619, 117423580140, (.direct 10180561190 16271159185), (.chord (.midpoint ⟨309816954407, 241506453765, 221238226383, 320650816143, 262055865585, 81948750040⟩) 10180665226 24716235638)⟩))
                      (.covered)))
                  (.cut 2 (7/32)
                    (.original (.row ⟨114055813619, 117423580140, (.direct 30541785600 37986365340), (.variance 587736766500)⟩))
                    (.original (.row ⟨114055813619, 117423580140, (.direct 30541785600 37986365340), (.chord (.midpoint ⟨285397034985, 264505297587, 231288058576, 310701759598, 271003134901, 93791494951⟩) 24716235638 43500686443)⟩)))))
              (.covered)))
          (.covered))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (1/2)
              (.original (.row ⟨114055813619, 117423580140, (.direct 91625662891 98870173315), (.variance 466073336752)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 174227225485 178776079261), (.variance 360545742722)⟩)))
            (.cut 3 (1/2)
              (.original (.row ⟨114055813619, 117423580140, (.direct 91625662891 98870173315), (.variance 466073336752)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 174227225485 178776079261), (.variance 360545742722)⟩))))
          (.cut 3 (1/2)
            (.original (.row ⟨114055813619, 117423580140, (.direct 91625662891 98870173315), (.chord (.midpoint ⟨394764933761, 171820373160, 185775592079, 362964429745, 231113363683, 165807116997⟩) 91625974997 274877906944)⟩))
            (.original (.row ⟨114055813619, 117423580140, (.direct 174227225485 178776079261), (.variance 360545742722)⟩))))))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.original (.cone))
            (.original (.row ⟨114055813619, 117423580140, .zero, (.variance 308027857569)⟩)))
          (.original (.row ⟨114055813619, 117423580140, .zero, (.variance 308027857569)⟩)))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.original (.row ⟨114055813619, 117423580140, (.direct 391506126583 385420613501), (.variance 251594246364)⟩))
                (.original (.row ⟨114055813619, 117423580140, (.direct 488587506629 477048116953), (.variance 237928099262)⟩)))
              (.original (.row ⟨114055813619, 117423580140, (.direct 593382169971 575692350726), (.variance 226501409539)⟩)))
            (.cut 3 (13/8)
              (.original (.row ⟨114055813619, 117423580140, (.direct 391506126583 385420613501), (.variance 251594246364)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 593382169971 575692350726), (.variance 226501409539)⟩))))
          (.original (.row ⟨114055813619, 117423580140, (.direct 391506126583 385420613501), (.variance 251594246364)⟩))))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 792728544161), (.variance 208300466975)⟩))
                  (.original (.row ⟨114055813619, 117423580140, (.direct 1082810704946 1034358052294), (.variance 194282535521)⟩)))
                (.original (.row ⟨114055813619, 117423580140, (.direct 1366046989981 1298914978048), (.variance 183034797948)⟩)))
              (.original (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1891708949956), (.variance 165874469856)⟩)))
            (.cut 3 (13/2)
              (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3306396652069), (.variance 143310952281)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 5340438828596 4992557608432), (.variance 128651709564)⟩))))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 792728544161), (.variance 208300466975)⟩))
                  (.original (.row ⟨114055813619, 117423580140, (.direct 1082810704946 1034358052294), (.variance 194282535521)⟩)))
                (.original (.row ⟨114055813619, 117423580140, (.direct 1366046989981 1298914978048), (.variance 183034797948)⟩)))
              (.cut 3 (17/4)
                (.original (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1891708949956), (.variance 165874469856)⟩))
                (.original (.row ⟨114055813619, 117423580140, (.direct 2723407729414 2562883569759), (.variance 153196007455)⟩))))
            (.cut 3 (13/2)
              (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3306396652069), (.variance 143310952281)⟩))
              (.original (.row ⟨114055813619, 117423580140, (.direct 5340438828596 4992557608432), (.variance 128651709564)⟩)))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 792728544161), (.variance 208300466975)⟩))
            (.original (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1891708949956), (.variance 165874469856)⟩)))
          (.cut 3 (13/2)
            (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3306396652069), (.variance 143310952281)⟩))
            (.original (.row ⟨114055813619, 117423580140, (.direct 5340438828596 4992557608432), (.variance 128651709564)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop1H7PosRest_ok : CutTop1H7PosRestTree.geometryOK CutTop1H7PosPowerCache CutTop1H7PosRestBox true (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
