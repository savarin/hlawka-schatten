/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0NegRestPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0NegRestPart3Box : Box := ((((((((((⟨![0, 9/100, 0, -8], ![9/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).upperChild 1 (1/10)).lowerChild 1 (21/200)

set_option maxRecDepth 16000 in
def CutMid2H0NegRestPart3Tree : RatioRemainder :=
  .cut 0 (9/136)
    (.cut 3 (1/16)
      (.cut 1 (41/400)
        (.cut 0 (9/272)
          (.cut 2 (1/16)
            (.original (.row ⟨91020629597, 92105866080, (.direct 3393509060 3538887117), (.chord .universal 0 3393555298)⟩))
            (.cut 3 (1/32)
              (.covered)
              (.original (.row ⟨91020629597, 92105866080, (.direct 3393509060 3538887117), (.chord (.secant 1590324456792 286649781134 24387849853 30541785600) 3393555298 10180665226)⟩))))
          (.cut 2 (1/16)
            (.original (.row ⟨91020629597, 92105866080, (.direct 3393509060 3686455911), (.chord .universal 0 3393555298)⟩))
            (.cut 3 (1/32)
              (.covered)
              (.original (.row ⟨91020629597, 92105866080, (.direct 3393509060 3686455911), (.chord (.secant 1585099875175 283877121161 20990012578 33196091065) 3393555298 10180665226)⟩)))))
        (.cut 0 (9/272)
          (.cut 2 (1/16)
            (.original (.row ⟨92105866079, 93177423805, (.direct 3393509060 3542657839), (.chord .universal 0 3393555298)⟩))
            (.cut 3 (1/32)
              (.covered)
              (.original (.row ⟨92105866079, 93177423805, (.direct 3393509060 3542657839), (.chord (.secant 1590899226182 286955209561 24387849853 30541785600) 3393555298 10180665226)⟩))))
          (.cut 1 (83/800)
            (.cut 2 (1/16)
              (.original (.row ⟨92105866079, 92643323332, (.direct 3393509060 3690281375), (.chord .universal 0 3393555298)⟩))
              (.cut 3 (1/32)
                (.covered)
                (.original (.row ⟨92105866079, 92643323332, (.direct 3393509060 3690281375), (.chord (.secant 1585673568570 284181255611 21050005388 33267132821) 3393555298 10180665226)⟩))))
            (.cut 3 (1/32)
              (.cut 2 (1/16)
                (.original (.row ⟨92643323331, 93177423805, (.direct 1131165907 1341655312), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨92643323331, 93177423805, (.direct 3393509060 3694113352), (.chord .universal 0 3393555298)⟩))
                (.original (.row ⟨92643323331, 93177423805, (.direct 3393509060 3694113352), (.chord (.secant 1586248095583 284485911708 21080084868 33302745015) 3393555298 10180665226)⟩)))))))
      (.cut 3 (3/32)
        (.cut 2 (1/16)
          (.original (.row ⟨91020629597, 93177423805, (.direct 6452795533 6819131005), (.variance 868750156237)⟩))
          (.cut 2 (3/32)
            (.original (.row ⟨91020629597, 93177423805, (.direct 6452795533 6819131005), (.chord (.secant 2050443585738 552349466344 122484193608 144557604977) 3393555298 6452870597)⟩))
            (.original (.row ⟨91020629597, 93177423805, (.direct 6452795533 6819131005), (.chord (.secant 1597521202008 290479784102 73163544754 91625662891) 6452870597 10180665226)⟩))))
        (.cut 2 (1/16)
          (.original (.row ⟨91020629597, 93177423805, (.direct 10180561190 10597931833), (.variance 734193276773)⟩))
          (.cut 2 (3/32)
            (.original (.row ⟨91020629597, 93177423805, (.direct 10180561190 10597931833), (.chord (.secant 2524428178222 858432253029 246609998779 274877906944) 3393555298 6452870597)⟩))
            (.original (.row ⟨91020629597, 93177423805, (.direct 10180561190 10597931833), (.chord (.secant 1883287870109 451448278164 150498559827 174227225485) 6452870597 10180665226)⟩))))))
    (.cut 3 (1/16)
      (.cut 1 (41/400)
        (.cut 0 (27/272)
          (.cut 1 (81/800)
            (.cut 2 (1/16)
              (.original (.row ⟨91020629597, 91564989626, (.direct 3393509060 3830425117), (.chord .universal 0 3393555298)⟩))
              (.cut 3 (1/32)
                (.covered)
                (.original (.row ⟨91020629597, 91564989626, (.direct 3393509060 3830425117), (.chord (.secant 1579023423044 280660685531 17784118319 35931155045) 3393555298 10180665226)⟩))))
            (.cut 2 (1/16)
              (.original (.row ⟨91564989625, 92105866080, (.direct 3393509060 3836237874), (.chord .universal 0 3393555298)⟩))
              (.cut 3 (1/32)
                (.covered)
                (.original (.row ⟨91564989625, 92105866080, (.direct 3393509060 3836237874), (.chord (.secant 1579881641459 281114420116 17840517453 36004253717) 3393555298 10180665226)⟩)))))
          (.cut 1 (81/800)
            (.cut 2 (1/16)
              (.original (.row ⟨91020629597, 91564989626, (.direct 3393509060 3980348433), (.chord .universal 0 3393555298)⟩))
              (.cut 3 (1/32)
                (.covered)
                (.original (.row ⟨91020629597, 91564989626, (.direct 3393509060 3980348433), (.chord (.secant 1573526903093 277758978667 14778703607 38745319538) 3393555298 10180665226)⟩))))
            (.cut 3 (1/32)
              (.cut 2 (1/16)
                (.original (.row ⟨91564989625, 92105866080, (.direct 1131165907 1553575562), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨91564989625, 92105866080, (.direct 3393509060 3988210042), (.variance 1087543557030)⟩))
                (.original (.row ⟨91564989625, 92105866080, (.direct 3393509060 3988210042), (.chord (.secant 1574669761127 278361703538 14857747054 38858080097) 3393555298 10180665226)⟩))))))
        (.cut 0 (27/272)
          (.cut 1 (83/800)
            (.cut 3 (1/32)
              (.cut 2 (1/16)
                (.original (.row ⟨92105866079, 92643323332, (.direct 1131165907 1447579818), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨92105866079, 92643323332, (.direct 3393509060 3842061553), (.variance 1108894576218)⟩))
                (.original (.row ⟨92105866079, 92643323332, (.direct 3393509060 3842061553), (.chord (.secant 1580741163778 281569023887 17897056905 36077503623) 3393555298 10180665226)⟩))))
            (.cut 3 (1/32)
              (.cut 2 (1/16)
                (.original (.row ⟨92643323331, 93177423805, (.direct 1131165907 1451786190), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨92643323331, 93177423805, (.direct 3393509060 3847896182), (.variance 1108304553205)⟩))
                (.original (.row ⟨92643323331, 93177423805, (.direct 3393509060 3847896182), (.chord (.secant 1581601992898 282024498986 17953737028 36150905139) 3393555298 10180665226)⟩)))))
          (.cut 1 (83/800)
            (.cut 3 (1/32)
              (.cut 2 (1/16)
                (.original (.row ⟨92105866079, 92643323332, (.direct 1131165907 1559325514), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨92105866079, 92643323332, (.direct 3393509060 3996087750), (.variance 1086716698629)⟩))
                (.original (.row ⟨92105866079, 92643323332, (.direct 3393509060 3996087750), (.chord (.secant 1575814432713 278965706032 14937050455 38971110355) 3393555298 10180665226)⟩))))
            (.cut 3 (1/32)
              (.cut 0 (63/544)
                (.cut 2 (1/16)
                  (.original (.row ⟨92643323331, 93177423805, (.direct 1131165907 1508045782), (.chord .universal 0 3393555298)⟩))
                  (.covered))
                (.cut 2 (1/16)
                  (.original (.row ⟨92643323331, 93177423805, (.direct 1131165907 1565090902), (.chord .universal 0 3393555298)⟩))
                  (.covered)))
              (.cut 2 (1/16)
                (.original (.row ⟨92643323331, 93177423805, (.direct 3393509060 4003981599), (.variance 1085890893780)⟩))
                (.original (.row ⟨92643323331, 93177423805, (.direct 3393509060 4003981599), (.chord (.secant 1576960921990 279570989359 15016614413 39084410993) 3393555298 10180665226)⟩)))))))
      (.cut 3 (3/32)
        (.cut 2 (1/16)
          (.original (.row ⟨91020629597, 93177423805, (.direct 6452795533 7192800544), (.variance 850580915997)⟩))
          (.cut 2 (3/32)
            (.original (.row ⟨91020629597, 93177423805, (.direct 6452795533 7192800544), (.chord (.secant 2038558357872 545035235165 112505950957 156709450665) 3393555298 6452870597)⟩))
            (.original (.row ⟨91020629597, 93177423805, (.direct 6452795533 7192800544), (.chord (.secant 1571962908664 276934673461 62749963393 99327927443) 6452870597 10180665226)⟩))))
        (.cut 3 (7/64)
          (.cut 2 (1/16)
            (.original (.row ⟨91020629597, 93177423805, (.direct 8238656156 9032032236), (.variance 724171769111)⟩))
            (.original (.row ⟨91020629597, 93177423805, (.direct 8238656156 9032032236), (.chord (.secant 2269656112304 690650822917 136474931833 183615794396) 3393555298 10180665226)⟩)))
          (.cut 0 (27/272)
            (.original (.row ⟨91020629597, 93177423805, (.direct 10180561190 10808876727), (.variance 680744323520)⟩))
            (.original (.row ⟨91020629597, 93177423805, (.direct 10180561190 11021352075), (.variance 676885885436)⟩))))))

set_option maxRecDepth 16000 in
theorem CutMid2H0NegRestPart3_ok : CutMid2H0NegRestPart3Tree.ok CutMid2H0NegRestPart3Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
