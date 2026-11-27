/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H7PosPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H7PosRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H7PosRestBox : Box := ⟨![63/136, 17/100, 0, -8], ![9/17, 9/50, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop2H7PosRestTree : RatioRemainder :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (-5)
              (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3179190521514), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 724368574225), (.variance 213277869378)⟩)))
            (.cut 3 (-5)
              (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3179190521514), (.variance 144790805055)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 724368574225), (.variance 213277869378)⟩))))
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 724368574225), (.variance 213277869378)⟩)))
        (.cut 2 (1/2)
          (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 18878216662), (.variance 554280204246)⟩))
          (.cut 2 (3/4)
            (.cut 3 (-9/8)
              (.original (.row ⟨117423580139, 120689819475, (.direct 331294831298 280886417403), (.variance 273325891851)⟩))
              (.cut 3 (-11/16)
                (.original (.row ⟨117423580139, 120689819475, (.direct 151782739331 122049106225), (.variance 339995284754)⟩))
                (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 18878216662), (.chord .universal 91625974997 174227471798)⟩))))
            (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 18878216662), (.chord .universal 174227471798 274877906944)⟩)))))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (0)
              (.original (.row ⟨117423580139, 120689819475, (.direct 0 2563271455), (.chord .universal 0 10180665226)⟩))
              (.cut 3 (1/8)
                (.original (.row ⟨117423580139, 120689819475, (.direct 10180561190 16700147583), (.variance 1014295304428)⟩))
                (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 38487961339), (.variance 584110430723)⟩))))
            (.cut 2 (5/16)
              (.cut 3 (0)
                (.cut 1 (7/40)
                  (.cut 1 (69/400)
                    (.cut 3 (-1/8)
                      (.original (.row ⟨117423580139, 118249306650, (.direct 10180561190 3949825824), (.chord .universal 10180665226 43500686443)⟩))
                      (.covered))
                    (.cut 3 (-1/8)
                      (.original (.row ⟨118249306649, 119068833411, (.direct 10180561190 3868866870), (.chord .universal 10180665226 43500686443)⟩))
                      (.covered)))
                  (.cut 1 (71/400)
                    (.cut 3 (-1/8)
                      (.original (.row ⟨119068833410, 119882294556, (.direct 10180561190 3788308847), (.chord .universal 10180665226 43500686443)⟩))
                      (.covered))
                    (.cut 3 (-1/8)
                      (.original (.row ⟨119882294555, 120689819475, (.direct 10180561190 3708159441), (.chord .universal 10180665226 43500686443)⟩))
                      (.covered))))
                (.cut 3 (1/8)
                  (.cut 3 (1/16)
                    (.covered)
                    (.cut 2 (7/32)
                      (.original (.row ⟨117423580139, 120689819475, (.direct 10180561190 16700147583), (.chord (.midpoint ⟨304464761474, 246422540783, 223442246526, 318403487891, 264012135644, 73166663727⟩) 10180665226 24716235638)⟩))
                      (.covered)))
                  (.cut 2 (7/32)
                    (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 38487961339), (.variance 584110430723)⟩))
                    (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 38487961339), (.chord (.midpoint ⟨282001231196, 267822070828, 232685273552, 309376877857, 272252407743, 89977855888⟩) 24716235638 43500686443)⟩)))))
              (.covered)))
          (.covered))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (1/2)
              (.original (.row ⟨117423580139, 120689819475, (.direct 91625662891 99345420752), (.variance 464656156428)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 174227225485 179071593741), (.variance 360150696431)⟩)))
            (.cut 3 (1/2)
              (.original (.row ⟨117423580139, 120689819475, (.direct 91625662891 99345420752), (.variance 464656156428)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 174227225485 179071593741), (.variance 360150696431)⟩))))
          (.cut 3 (1/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 91625662891 99345420752), (.chord (.midpoint ⟨393737880167, 172576895334, 186213369324, 362358790105, 231488406758, 165074267191⟩) 91625974997 274877906944)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 174227225485 179071593741), (.variance 360150696431)⟩))))))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.original (.cone))
            (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 307912233455)⟩)))
          (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 307912233455)⟩)))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 385028422461), (.variance 251661328111)⟩))
                  (.original (.row ⟨117423580139, 120689819475, (.direct 439055879922 429772161961), (.variance 244519813923)⟩)))
                (.original (.row ⟨117423580139, 120689819475, (.direct 488587506629 476305647429), (.variance 238025161638)⟩)))
              (.original (.row ⟨117423580139, 120689819475, (.direct 593382169971 574555577717), (.variance 226618671653)⟩)))
            (.cut 3 (13/8)
              (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 385028422461), (.variance 251661328111)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 593382169971 574555577717), (.variance 226618671653)⟩))))
          (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 385028422461), (.variance 251661328111)⟩))))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 790681997305), (.variance 208441511949)⟩))
                  (.original (.row ⟨117423580139, 120689819475, (.direct 1082810704946 1031253952494), (.variance 194435497644)⟩)))
                (.original (.row ⟨117423580139, 120689819475, (.direct 1366046989981 1294618117835), (.variance 183193679655)⟩)))
              (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1884657487211), (.variance 166036759005)⟩)))
            (.cut 3 (13/2)
              (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3292533498421), (.variance 143468713204)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 4970365599638), (.variance 128801875500)⟩))))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 790681997305), (.variance 208441511949)⟩))
                  (.original (.row ⟨117423580139, 120689819475, (.direct 1082810704946 1031253952494), (.variance 194435497644)⟩)))
                (.original (.row ⟨117423580139, 120689819475, (.direct 1366046989981 1294618117835), (.variance 183193679655)⟩)))
              (.cut 3 (17/4)
                (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1884657487211), (.variance 166036759005)⟩))
                (.original (.row ⟨117423580139, 120689819475, (.direct 2723407729414 2552630076748), (.variance 153356905425)⟩))))
            (.cut 3 (13/2)
              (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3292533498421), (.variance 143468713204)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 4970365599638), (.variance 128801875500)⟩)))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 790681997305), (.variance 208441511949)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1884657487211), (.variance 166036759005)⟩)))
          (.cut 3 (13/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3292533498421), (.variance 143468713204)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 4970365599638), (.variance 128801875500)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop2H7PosRest_ok : CutTop2H7PosRestTree.geometryOK CutTop2H7PosPowerCache CutTop2H7PosRestBox true (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
