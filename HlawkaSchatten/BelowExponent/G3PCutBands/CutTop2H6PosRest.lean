/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H6PosRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H6PosRestBox : Box := ⟨![27/68, 17/100, 0, -8], ![63/136, 9/50, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop2H6PosRestTree : RatioRemainder :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (-5)
              (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3221522351205), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 736638677859), (.variance 212341840852)⟩)))
            (.cut 3 (-5)
              (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3221522351205), (.variance 144290164442)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 736638677859), (.variance 212341840852)⟩))))
          (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 736638677859), (.variance 212341840852)⟩)))
        (.cut 2 (1/2)
          (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 20221724010), (.variance 544391043063)⟩))
          (.cut 3 (-9/8)
            (.original (.row ⟨117423580139, 120689819475, (.direct 331294831298 287018749459), (.variance 271784503711)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 20221724010), (.chord .universal 91625974997 274877906944)⟩)))))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (0)
              (.original (.row ⟨117423580139, 120689819475, (.direct 0 2074338105), (.chord .universal 0 10180665226)⟩))
              (.cut 3 (1/8)
                (.original (.row ⟨117423580139, 120689819475, (.direct 10180561190 15821474095), (.chord .universal 0 10180665226)⟩))
                (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 37457952010), (.variance 592320457815)⟩))))
            (.cut 2 (5/16)
              (.cut 3 (0)
                (.cut 1 (7/40)
                  (.cut 1 (69/400)
                    (.cut 2 (7/32)
                      (.original (.row ⟨117423580139, 118249306650, (.direct 0 1926430311), (.chord .universal 10180665226 24716235638)⟩))
                      (.covered))
                    (.cut 2 (7/32)
                      (.original (.row ⟨118249306649, 119068833411, (.direct 0 1975149347), (.chord .universal 10180665226 24716235638)⟩))
                      (.covered)))
                  (.cut 1 (71/400)
                    (.cut 2 (7/32)
                      (.original (.row ⟨119068833410, 119882294556, (.direct 0 2024451495), (.chord .universal 10180665226 24716235638)⟩))
                      (.covered))
                    (.cut 3 (-1/8)
                      (.original (.row ⟨119882294555, 120689819475, (.direct 10180561190 4383904608), (.chord .universal 10180665226 43500686443)⟩))
                      (.covered))))
                (.cut 3 (1/8)
                  (.cut 3 (1/16)
                    (.covered)
                    (.cut 2 (7/32)
                      (.original (.row ⟨117423580139, 120689819475, (.direct 10180561190 15821474095), (.chord (.midpoint ⟨347374107521, 208844672748, 212169509364, 330315748847, 248372472575, 112173824142⟩) 10180665226 24716235638)⟩))
                      (.covered)))
                  (.cut 2 (7/32)
                    (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 37457952010), (.variance 592320457815)⟩))
                    (.original (.row ⟨117423580139, 120689819475, (.direct 30541785600 37457952010), (.chord (.midpoint ⟨319546932249, 232741483032, 223451547546, 318394084443, 258504705087, 118360027228⟩) 24716235638 43500686443)⟩)))))
              (.covered)))
          (.covered))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (1/2)
              (.original (.row ⟨117423580139, 120689819475, (.direct 91625662891 98367922350), (.variance 467843041309)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 174227225485 178463399670), (.variance 361035386258)⟩)))
            (.cut 3 (1/2)
              (.original (.row ⟨117423580139, 120689819475, (.direct 91625662891 98367922350), (.variance 467843041309)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 174227225485 178463399670), (.variance 361035386258)⟩))))
          (.cut 3 (1/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 91625662891 98367922350), (.chord (.midpoint ⟨429528535794, 147336080771, 178096421172, 374000230361, 218365364195, 181303775820⟩) 91625974997 274877906944)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 174227225485 178463399670), (.variance 361035386258)⟩))))))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.original (.cone))
            (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 308170775095)⟩)))
          (.original (.row ⟨117423580139, 120689819475, .zero, (.variance 308170775095)⟩)))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 385836006347), (.variance 251523289962)⟩))
                  (.original (.row ⟨117423580139, 120689819475, (.direct 439055879922 430928698514), (.variance 244347801180)⟩)))
                (.original (.row ⟨117423580139, 120689819475, (.direct 488587506629 477834671633), (.variance 237825481393)⟩)))
              (.original (.row ⟨117423580139, 120689819475, (.direct 593382169971 576896812691), (.variance 226377483443)⟩)))
            (.cut 3 (13/8)
              (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 385836006347), (.variance 251523289962)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 593382169971 576896812691), (.variance 226377483443)⟩))))
          (.original (.row ⟨117423580139, 120689819475, (.direct 391506126583 385836006347), (.variance 251523289962)⟩))))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 794897452831), (.variance 208151489639)⟩))
                  (.original (.row ⟨117423580139, 120689819475, (.direct 1082810704946 1037648269014), (.variance 194121033127)⟩)))
                (.original (.row ⟨117423580139, 120689819475, (.direct 1366046989981 1303470003115), (.variance 182867092846)⟩)))
              (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1899185273128), (.variance 165703234190)⟩)))
            (.cut 3 (13/2)
              (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3321097681921), (.variance 143144565725)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5016093139987), (.variance 128493370008)⟩))))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 794897452831), (.variance 208151489639)⟩))
                  (.original (.row ⟨117423580139, 120689819475, (.direct 1082810704946 1037648269014), (.variance 194121033127)⟩)))
                (.original (.row ⟨117423580139, 120689819475, (.direct 1366046989981 1303470003115), (.variance 182867092846)⟩)))
              (.cut 3 (17/4)
                (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1899185273128), (.variance 165703234190)⟩))
                (.original (.row ⟨117423580139, 120689819475, (.direct 2723407729414 2573755979917), (.variance 153026282336)⟩))))
            (.cut 3 (13/2)
              (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3321097681921), (.variance 143144565725)⟩))
              (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5016093139987), (.variance 128493370008)⟩)))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 824633666698 794897452831), (.variance 208151489639)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1899185273128), (.variance 165703234190)⟩)))
          (.cut 3 (13/2)
            (.original (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3321097681921), (.variance 143144565725)⟩))
            (.original (.row ⟨117423580139, 120689819475, (.direct 5340438828596 5016093139987), (.variance 128493370008)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop2H6PosRest_ok : CutTop2H6PosRestTree.ok CutTop2H6PosRestBox true (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
