/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H3NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H3NegPart1Box : Box := ((((((⟨![27/136, 17/100, 0, -8], ![9/34, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop2H3NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨117423580139, 120689819475, (.direct 0 854423875), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 1 (7/40)
          (.cut 0 (63/272)
            (.cut 1 (69/400)
              (.cut 3 (1/32)
                (.row ⟨117423580139, 118249306650, (.direct 1131165907 2568710016), (.chord .universal 0 10180665226)⟩)
                (.cut 2 (1/16)
                  (.row ⟨117423580139, 118249306650, (.direct 3393509060 5319713407), (.variance 960130859119)⟩)
                  (.row ⟨117423580139, 118249306650, (.direct 3393509060 5319713407), (.chord (.secant 1676609100680 333355897192 15251909105 62537892356) 3393555298 10180665226)⟩)))
              (.cut 3 (1/32)
                (.row ⟨118249306649, 119068833411, (.direct 1131165907 2594880103), (.chord .universal 0 10180665226)⟩)
                (.cut 2 (1/16)
                  (.row ⟨118249306649, 119068833411, (.direct 3393509060 5352821869), (.variance 957807607294)⟩)
                  (.row ⟨118249306649, 119068833411, (.direct 3393509060 5352821869), (.chord (.secant 1681034103272 335795801905 15598061063 63119163129) 3393555298 10180665226)⟩))))
            (.cut 1 (69/400)
              (.cut 3 (1/32)
                (.row ⟨117423580139, 118249306650, (.direct 1131165907 2807594732), (.chord .universal 0 10180665226)⟩)
                (.cut 2 (1/16)
                  (.row ⟨117423580139, 118249306650, (.direct 3393509060 5620225662), (.variance 936960229664)⟩)
                  (.row ⟨117423580139, 118249306650, (.direct 3393509060 5620225662), (.chord (.secant 1688308867681 339816116561 13886785177 68652835894) 3393555298 10180665226)⟩)))
              (.cut 3 (1/32)
                (.row ⟨118249306649, 119068833411, (.direct 1131165907 2838505922), (.chord .universal 0 10180665226)⟩)
                (.cut 2 (1/16)
                  (.row ⟨118249306649, 119068833411, (.direct 3393509060 5658843740), (.variance 934467399128)⟩)
                  (.row ⟨118249306649, 119068833411, (.direct 3393509060 5658843740), (.chord (.secant 1693379349382 342624890162 14277276093 69354860626) 3393555298 10180665226)⟩)))))
          (.cut 0 (63/272)
            (.cut 1 (71/400)
              (.cut 3 (1/32)
                (.row ⟨119068833410, 119882294556, (.direct 1131165907 2621220165), (.chord .universal 0 10180665226)⟩)
                (.cut 2 (1/16)
                  (.row ⟨119068833410, 119882294556, (.direct 3393509060 5386097228), (.variance 955497123963)⟩)
                  (.row ⟨119068833410, 119882294556, (.direct 3393509060 5386097228), (.chord (.secant 1685475566638 338248988131 15948031785 63704016962) 3393555298 10180665226)⟩)))
              (.cut 3 (1/32)
                (.row ⟨119882294555, 120689819475, (.direct 1131165907 2647731046), (.chord .universal 0 10180665226)⟩)
                (.cut 2 (1/16)
                  (.row ⟨119882294555, 120689819475, (.direct 3393509060 5419540362), (.variance 953199272035)⟩)
                  (.row ⟨119882294555, 120689819475, (.direct 3393509060 5419540362), (.chord (.secant 1689933573440 340715525173 16301832092 64292471977) 3393555298 10180665226)⟩))))
            (.cut 1 (71/400)
              (.cut 3 (1/32)
                (.row ⟨119068833410, 119882294556, (.direct 1131165907 2869627170), (.chord .universal 0 10180665226)⟩)
                (.cut 2 (1/16)
                  (.row ⟨119068833410, 119882294556, (.direct 3393509060 5697665680), (.variance 931990299345)⟩)
                  (.row ⟨119068833410, 119882294556, (.direct 3393509060 5697665680), (.chord (.secant 1698469374624 345449928656 14672835373 70061452037) 3393555298 10180665226)⟩)))
              (.cut 3 (1/32)
                (.row ⟨119882294555, 120689819475, (.direct 1131165907 2900959498), (.chord .universal 0 10180665226)⟩)
                (.cut 2 (1/16)
                  (.row ⟨119882294555, 120689819475, (.direct 3393509060 5736692550), (.variance 929528740345)⟩)
                  (.row ⟨119882294555, 120689819475, (.direct 3393509060 5736692550), (.chord (.secant 1703579042738 348291315901 15073471682 70772632766) 3393555298 10180665226)⟩))))))
        (.cut 3 (3/32)
          (.cut 3 (5/64)
            (.row ⟨117423580139, 120689819475, (.direct 4833349683 7405540992), (.variance 785005310896)⟩)
            (.row ⟨117423580139, 120689819475, (.direct 6452795533 9226573102), (.variance 729764208977)⟩))
          (.row ⟨117423580139, 120689819475, (.direct 10180561190 13292427162), (.variance 685866822675)⟩)))
      (.cut 3 (3/16)
        (.cut 3 (5/32)
          (.row ⟨117423580139, 120689819475, (.direct 14500097491 17881085976), (.variance 619541582574)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 19358451269 22953169354), (.variance 570982083100)⟩))
        (.row ⟨117423580139, 120689819475, (.direct 30541785600 34430318928), (.variance 533351110438)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H3NegPart1_checked : CutTop2H3NegPart1Tree.commonOK CutTop2H3NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
