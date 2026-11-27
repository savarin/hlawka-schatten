/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H0NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H0NegPart1Box : Box := ((((((⟨![0, 17/100, 0, -8], ![9/136, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop2H0NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨117423580139, 120689819475, (.direct 0 94935999), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 1 (7/40)
        (.cut 3 (1/16)
          (.cut 0 (9/272)
            (.cut 1 (69/400)
              (.cut 3 (1/32)
                (.row ⟨117423580139, 118249306650, (.direct 1131165907 1309625170), (.chord .universal 0 10180665226)⟩)
                (.row ⟨117423580139, 118249306650, (.direct 3393509060 3648968586), (.chord .universal 0 10180665226)⟩))
              (.cut 3 (1/32)
                (.row ⟨118249306649, 119068833411, (.direct 1131165907 1312536514), (.chord .universal 0 10180665226)⟩)
                (.row ⟨118249306649, 119068833411, (.direct 3393509060 3653080179), (.chord .universal 0 10180665226)⟩)))
            (.cut 1 (69/400)
              (.cut 3 (1/32)
                (.row ⟨117423580139, 118249306650, (.direct 1131165907 1497530215), (.chord .universal 0 10180665226)⟩)
                (.cut 2 (1/16)
                  (.row ⟨117423580139, 118249306650, (.direct 3393509060 3911158056), (.chord .universal 0 3393555298)⟩)
                  (.row ⟨117423580139, 118249306650, (.direct 3393509060 3911158056), (.chord (.secant 1618562198245 301747728479 22757307277 35281320720) 3393555298 10180665226)⟩)))
              (.cut 3 (1/32)
                (.row ⟨118249306649, 119068833411, (.direct 1131165907 1503650378), (.chord .universal 0 10180665226)⟩)
                (.row ⟨118249306649, 119068833411, (.direct 3393509060 3919596155), (.chord .universal 0 10180665226)⟩))))
          (.cut 3 (3/32)
            (.cut 2 (1/16)
              (.row ⟨117423580139, 119068833411, (.direct 6452795533 7091408349), (.variance 868750156237)⟩)
              (.row ⟨117423580139, 119068833411, (.direct 6452795533 7091408349), (.chord (.secant 2086085768695 574403925439 73163544754 91625662891) 3393555298 10180665226)⟩))
            (.cut 3 (7/64)
              (.cut 2 (1/16)
                (.row ⟨117423580139, 119068833411, (.direct 8238656156 8923610318), (.variance 734193276773)⟩)
                (.row ⟨117423580139, 119068833411, (.direct 8238656156 8923610318), (.chord (.secant 2319327625827 722812245916 150498559827 174227225485) 3393555298 10180665226)⟩))
              (.cut 2 (1/16)
                (.row ⟨117423580139, 119068833411, (.direct 10180561190 10906677961), (.variance 688691889909)⟩)
                (.row ⟨117423580139, 119068833411, (.direct 10180561190 10906677961), (.chord (.secant 2561568496012 883440682842 196377413490 222445945561) 3393555298 10180665226)⟩)))))
        (.cut 3 (1/16)
          (.cut 0 (9/272)
            (.cut 1 (71/400)
              (.row ⟨119068833410, 119882294556, (.direct 3393509060 3657204767), (.chord .universal 0 10180665226)⟩)
              (.row ⟨119882294555, 120689819475, (.direct 3393509060 3661342412), (.chord .universal 0 10180665226)⟩))
            (.cut 1 (71/400)
              (.cut 3 (1/32)
                (.row ⟨119068833410, 119882294556, (.direct 1131165907 1509796576), (.chord .universal 0 10180665226)⟩)
                (.row ⟨119068833410, 119882294556, (.direct 3393509060 3928064141), (.chord .universal 0 10180665226)⟩))
              (.row ⟨119882294555, 120689819475, (.direct 3393509060 3936562161), (.chord .universal 0 10180665226)⟩)))
          (.cut 3 (3/32)
            (.cut 2 (1/16)
              (.row ⟨119068833410, 120689819475, (.direct 6452795533 7111815047), (.variance 868750156237)⟩)
              (.row ⟨119068833410, 120689819475, (.direct 6452795533 7111815047), (.chord (.secant 2088745600155 576056867470 73163544754 91625662891) 3393555298 10180665226)⟩))
            (.cut 3 (7/64)
              (.cut 2 (1/16)
                (.row ⟨119068833410, 120689819475, (.direct 8238656156 8945438686), (.variance 734193276773)⟩)
                (.row ⟨119068833410, 120689819475, (.direct 8238656156 8945438686), (.chord (.secant 2322045823889 724580343234 150498559827 174227225485) 3393555298 10180665226)⟩))
              (.row ⟨119068833410, 120689819475, (.direct 10180561190 10929770585), (.variance 688691889909)⟩)))))
      (.cut 3 (3/16)
        (.cut 3 (5/32)
          (.cut 3 (9/64)
            (.cut 1 (7/40)
              (.row ⟨117423580139, 119068833411, (.direct 12270063068 13032859415), (.variance 651562574406)⟩)
              (.row ⟨119068833410, 120689819475, (.direct 12270063068 13057079395), (.variance 651562574406)⟩))
            (.cut 1 (7/40)
              (.row ⟨117423580139, 119068833411, (.direct 14500097491 15295614402), (.variance 620477318811)⟩)
              (.row ⟨119068833410, 120689819475, (.direct 14500097491 15320840410), (.variance 620477318811)⟩)))
          (.cut 3 (11/64)
            (.row ⟨117423580139, 120689819475, (.direct 16864636136 17715445469), (.variance 593929411221)⟩)
            (.row ⟨117423580139, 120689819475, (.direct 19358451269 20236002713), (.variance 570893780246)⟩)))
        (.cut 3 (7/32)
          (.cut 3 (13/64)
            (.row ⟨117423580139, 120689819475, (.direct 21976949588 22878193151), (.variance 550644921433)⟩)
            (.row ⟨117423580139, 120689819475, (.direct 24716051037 25638164785), (.variance 532652607245)⟩))
          (.cut 3 (15/64)
            (.row ⟨117423580139, 120689819475, (.direct 27572097984 28512452464), (.variance 516518883525)⟩)
            (.row ⟨117423580139, 120689819475, (.direct 30541785600 31497915909), (.variance 501938304662)⟩)))))

set_option maxRecDepth 16000 in
theorem CutTop2H0NegPart1_checked : CutTop2H0NegPart1Tree.commonOK CutTop2H0NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
