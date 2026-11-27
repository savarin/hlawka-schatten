/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H4PosRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H4PosRestBox : Box := ⟨![9/34, 17/100, 0, -8], ![45/136, 9/50, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop2H4PosRestTree : RatioRemainder :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (-5)
              (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3306804207167), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 761406255512), (.variance 210511015968)⟩)))
            (.cut 3 (-5)
              (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3306804207167), (.variance 143306326991)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 761406255512), (.variance 210511015968)⟩))))
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 761406255512), (.variance 210511015968)⟩)))
        (.cut 2 (1/2)
          (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 23009515951), (.variance 526287977843)⟩))
          (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 23009515951), (.chord .universal 91625974997 274877906944)⟩))))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (0)
              (.original (.row ⟨117423580139, 120689819475, (.direct 0 1216948227), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 35429054793), (.chord .universal 0 10180665226)⟩)))
            (.cut 2 (5/16)
              (.cut 2 (7/32)
                (.cut 1 (7/40)
                  (.cut 3 (0)
                    (.original (.row ⟨117423580139, 119068833411, (.direct 0 1158757336), (.chord .universal 10180665226 24716235638)⟩))
                    (.cut 3 (1/8)
                      (.original (.row ⟨117423580139, 119068833411, (.direct 10180561190 13990607476), (.chord .universal 10180665226 24716235638)⟩))
                      (.original (.row ⟨117423580139, 119068833411, (.direct 30541785600 35276360756), (.variance 609998000820)⟩))))
                  (.cut 3 (0)
                    (.original (.row ⟨119068833410, 120689819475, (.direct 0 1216948227), (.chord .universal 10180665226 24716235638)⟩))
                    (.cut 3 (1/8)
                      (.original (.row ⟨119068833410, 120689819475, (.direct 10180561190 14117346429), (.chord .universal 10180665226 24716235638)⟩))
                      (.original (.row ⟨119068833410, 120689819475, (.direct 30541785600 35429054793), (.variance 608803638814)⟩)))))
                (.cut 1 (7/40)
                  (.cut 3 (0)
                    (.original (.row ⟨117423580139, 119068833411, (.direct 0 1158757336), (.chord .universal 24716235638 43500686443)⟩))
                    (.cut 3 (1/8)
                      (.covered)
                      (.original (.row ⟨117423580139, 119068833411, (.direct 30541785600 35276360756), (.chord (.midpoint ⟨399699868663, 168212462530, 204115752913, 339510844126, 229310271650, 164900676797⟩) 24716235638 43500686443)⟩))))
                  (.cut 3 (0)
                    (.covered)
                    (.cut 3 (1/8)
                      (.covered)
                      (.original (.row ⟨119068833410, 120689819475, (.direct 30541785600 35429054793), (.chord (.midpoint ⟨398590300230, 169019763447, 204556162782, 338992051829, 229715832261, 164110155975⟩) 24716235638 43500686443)⟩))))))
              (.covered)))
          (.covered))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.original (.row ⟨117423580139, 120689819475, (.direct 174227225485 177249304239), (.variance 474447262784)⟩))
            (.cut 3 (1/2)
              (.original (.row ⟨117423580139, 120689819475, (.direct 91625662891 96423650617), (.variance 474447262784)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 174227225485 177249304239), (.variance 362827234065)⟩))))
          (.cut 3 (1/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 91625662891 96423650617), (.chord (.midpoint ⟨504494506967, 101438577978, 161014379638, 401736930368, 190263269932, 211020968722⟩) 91625974997 274877906944)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 174227225485 177249304239), (.variance 362827234065)⟩))))))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.original (.cone))
            (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 308690086938)⟩)))
          (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 308690086938)⟩)))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 387453046792), (.variance 251247986261)⟩))
                  (.original (.row ⟨117423580139, 120689819475, (.direct 439055879922 433245210958), (.variance 244005009612)⟩)))
                (.original (.row ⟨117423580139, 120689819475, (.direct 488587506629 480898142247), (.variance 237427828052)⟩)))
              (.original (.row ⟨117423580139, 120689819475, (.direct 593382169971 581589814919), (.variance 225897720491)⟩)))
            (.cut 3 (13/8)
              (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 387453046792), (.variance 251247986261)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 593382169971 581589814919), (.variance 225897720491)⟩))))
          (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 387453046792), (.variance 251247986261)⟩))))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 803353153030), (.variance 207575547671)⟩))
                  (.original (.row ⟨117423580139, 120689819475, (.direct 1082810704946 1050480606704), (.variance 193497269810)⟩)))
                (.original (.row ⟨117423580139, 120689819475, (.direct 1366046989981 1321240460127), (.variance 182219828577)⟩)))
              (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1928364156755), (.variance 165042977878)⟩)))
            (.cut 3 (13/2)
              (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3378498728526), (.variance 142503688814)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5108010968656), (.variance 127883839192)⟩))))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 803353153030), (.variance 207575547671)⟩))
                  (.original (.row ⟨117423580139, 120689819475, (.direct 1082810704946 1050480606704), (.variance 193497269810)⟩)))
                (.original (.row ⟨117423580139, 120689819475, (.direct 1366046989981 1321240460127), (.variance 182219828577)⟩)))
              (.cut 3 (17/4)
                (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1928364156755), (.variance 165042977878)⟩))
                (.original (.row ⟨117423580139, 120689819475, (.direct 2723407729414 2616200230679), (.variance 152372259161)⟩))))
            (.cut 3 (13/2)
              (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3378498728526), (.variance 142503688814)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5108010968656), (.variance 127883839192)⟩)))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 803353153030), (.variance 207575547671)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1928364156755), (.variance 165042977878)⟩)))
          (.cut 3 (13/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3378498728526), (.variance 142503688814)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5108010968656), (.variance 127883839192)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop2H4PosRest_ok : CutTop2H4PosRestTree.ok CutTop2H4PosRestBox true (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
