/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H5NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H5NegPart0Box : Box := (((⟨![45/136, 17/100, 0, -8], ![27/68, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop2H5NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3264060482237), (.variance 143795377033)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 824633666698 748984681499), (.variance 211419671921)⟩))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.row ⟨117423580139, 120689819475, (.direct 5340438828596 4962068115712), (.variance 128858239268)⟩)
            (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3264060482237), (.variance 143795377033)⟩))
          (.cut 3 (-7/2)
            (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1844199212261), (.variance 166982951423)⟩)
            (.row ⟨117423580139, 120689819475, (.direct 824633666698 748984681499), (.variance 211419671921)⟩))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.row ⟨117423580139, 120689819475, (.direct 5340438828596 4962068115712), (.variance 128858239268)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 3523554676644 3264060482237), (.variance 143795377033)⟩))
        (.cut 3 (-7/2)
          (.row ⟨117423580139, 120689819475, (.direct 2002014560937 1844199212261), (.variance 166982951423)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 824633666698 748984681499), (.variance 211419671921)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨117423580139, 120689819475, (.direct 30541785600 21599016494), (.variance 535078684081)⟩)
        (.cut 3 (-9/8)
          (.row ⟨117423580139, 120689819475, (.direct 331294831298 293199824015), (.variance 270272355066)⟩)
          (.cut 3 (-11/16)
            (.row ⟨117423580139, 120689819475, (.direct 151782739331 129257456359), (.variance 334924633574)⟩)
            (.cut 3 (-15/32)
              (.row ⟨117423580139, 120689819475, (.direct 82716570280 67176229777), (.variance 397537455197)⟩)
              (.cut 2 (5/16)
                (.row ⟨117423580139, 120689819475, (.direct 30541785600 21599016494), (.variance 535078684081)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨117423580139, 120689819475, (.direct 54287234842 42073803193), (.chord (.midpoint ⟨300181341844, 250406458377, 237235593263, 305154786094, 265579477898, 121424715727⟩) 43500686443 91625974997)⟩)
                  (.row ⟨117423580139, 120689819475, (.direct 30541785600 21599016494), (.chord (.midpoint ⟨400125083662, 167903681348, 197294473849, 347798078250, 229154825800, 201209854467⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨117423580139, 120689819475, (.direct 331294831298 293199824015), (.variance 270272355066)⟩)
        (.cut 3 (-11/16)
          (.row ⟨117423580139, 120689819475, (.direct 151782739331 129257456359), (.variance 334924633574)⟩)
          (.cut 3 (-15/32)
            (.row ⟨117423580139, 120689819475, (.direct 82716570280 67176229777), (.variance 397537455197)⟩)
            (.cut 2 (3/4)
              (.row ⟨117423580139, 120689819475, (.direct 30541785600 21599016494), (.chord (.midpoint ⟨469195937185, 121927076869, 168534834348, 388933793061, 203630448923, 233340099314⟩) 91625974997 174227471798)⟩)
              (.row ⟨117423580139, 120689819475, (.direct 30541785600 21599016494), (.chord (.midpoint ⟨505232302436, 101030840256, 152770127385, 417001124066, 189980654716, 280962219032⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop2H5NegPart0_checked : CutTop2H5NegPart0Tree.commonOK CutTop2H5NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
