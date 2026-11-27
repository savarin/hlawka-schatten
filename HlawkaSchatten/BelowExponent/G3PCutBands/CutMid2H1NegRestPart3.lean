/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1NegRestPart3`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1NegRestPart3Box : Box := ((((((((((((⟨![9/68, 9/100, 0, -8], ![9/34, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).lowerChild 3 (1/16)).upperChild 1 (1/10)).lowerChild 1 (21/200)).lowerChild 0 (27/136)

set_option maxRecDepth 16000 in
def CutMid2H1NegRestPart3Tree : RatioRemainder :=
  .cut 1 (41/400)
    (.cut 0 (45/272)
      (.cut 1 (81/800)
        (.cut 3 (1/32)
          (.cut 2 (1/16)
            (.original (.row ⟨91020629597, 91564989626, (.direct 1131165907 1659375434), (.chord .universal 0 3393555298)⟩))
            (.covered))
          (.cut 2 (1/16)
            (.original (.row ⟨91020629597, 91564989626, (.direct 3393509060 4132385530), (.variance 1068049288281)⟩))
            (.original (.row ⟨91020629597, 91564989626, (.direct 3393509060 4132385530), (.chord (.secant 1568037460215 274868416791 11983759268 41637037183) 3393555298 10180665226)⟩))))
        (.cut 3 (1/32)
          (.cut 2 (1/16)
            (.original (.row ⟨91564989625, 92105866080, (.direct 1131165907 1666731073), (.chord .universal 0 3393555298)⟩))
            (.covered))
          (.cut 2 (1/16)
            (.original (.row ⟨91564989625, 92105866080, (.direct 3393509060 4142350242), (.variance 1067014476807)⟩))
            (.original (.row ⟨91564989625, 92105866080, (.direct 3393509060 4142350242), (.chord (.secant 1569464239679 275618997187 12081353958 41791454923) 3393555298 10180665226)⟩)))))
      (.cut 1 (81/800)
        (.cut 3 (1/32)
          (.cut 2 (1/16)
            (.original (.row ⟨91020629597, 91564989626, (.direct 1131165907 1773748226), (.chord .universal 0 3393555298)⟩))
            (.covered))
          (.cut 2 (1/16)
            (.original (.row ⟨91020629597, 91564989626, (.direct 3393509060 4286515760), (.variance 1048965249876)⟩))
            (.original (.row ⟨91020629597, 91564989626, (.direct 3393509060 4286515760), (.chord (.secant 1562555100889 271989021653 9411213091 44604859217) 3393555298 10180665226)⟩))))
        (.cut 3 (1/32)
          (.cut 0 (99/544)
            (.cut 2 (1/16)
              (.original (.row ⟨91564989625, 92105866080, (.direct 1131165907 1724403085), (.chord .universal 0 3393555298)⟩))
              (.covered))
            (.cut 2 (1/16)
              (.original (.row ⟨91564989625, 92105866080, (.direct 1131165907 1782795935), (.chord .universal 0 3393555298)⟩))
              (.covered)))
          (.cut 2 (1/16)
            (.original (.row ⟨91564989625, 92105866080, (.direct 3393509060 4298637050), (.variance 1047749249496)⟩))
            (.original (.row ⟨91564989625, 92105866080, (.direct 3393509060 4298637050), (.chord (.secant 1564265082630 272886320900 9522873510 44802875872) 3393555298 10180665226)⟩))))))
    (.cut 0 (45/272)
      (.cut 1 (83/800)
        (.cut 3 (1/32)
          (.cut 0 (81/544)
            (.cut 2 (1/16)
              (.original (.row ⟨92105866079, 92643323332, (.direct 1131165907 1616340903), (.chord .universal 0 3393555298)⟩))
              (.covered))
            (.cut 2 (1/16)
              (.original (.row ⟨92105866079, 92643323332, (.direct 1131165907 1674108434), (.chord .universal 0 3393555298)⟩))
              (.covered)))
          (.cut 2 (1/16)
            (.original (.row ⟨92105866079, 92643323332, (.direct 3393509060 4152336963), (.variance 1065981719030)⟩))
            (.original (.row ⟨92105866079, 92643323332, (.direct 3393509060 4152336963), (.chord (.secant 1570893380015 276371323753 12179369649 41946287398) 3393555298 10180665226)⟩))))
        (.cut 3 (1/32)
          (.cut 0 (81/544)
            (.cut 2 (1/16)
              (.original (.row ⟨92643323331, 93177423805, (.direct 1131165907 1622913950), (.chord .universal 0 3393555298)⟩))
              (.covered))
            (.cut 1 (167/1600)
              (.cut 2 (1/16)
                (.original (.row ⟨92643323331, 92910789338, (.direct 1131165907 1677805276), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨92910789337, 93177423805, (.direct 1131165907 1681507569), (.chord .universal 0 3393555298)⟩))
                (.covered))))
          (.cut 2 (1/16)
            (.original (.row ⟨92643323331, 93177423805, (.direct 3393509060 4162345749), (.variance 1064951006525)⟩))
            (.original (.row ⟨92643323331, 93177423805, (.direct 3393509060 4162345749), (.chord (.secant 1572324886733 277125400930 12277807131 42101535640) 3393555298 10180665226)⟩)))))
      (.cut 1 (83/800)
        (.cut 3 (1/32)
          (.cut 0 (99/544)
            (.cut 2 (1/16)
              (.original (.row ⟨92105866079, 92643323332, (.direct 1131165907 1732621219), (.chord .universal 0 3393555298)⟩))
              (.covered))
            (.cut 1 (33/320)
              (.cut 2 (1/16)
                (.original (.row ⟨92105866079, 92375018160, (.direct 1131165907 1787330637), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 2 (1/16)
                (.original (.row ⟨92375018159, 92643323332, (.direct 1131165907 1791872584), (.chord .universal 0 3393555298)⟩))
                (.covered))))
          (.cut 2 (1/16)
            (.original (.row ⟨92105866079, 92643323332, (.direct 3393509060 4310786973), (.variance 1046536449118)⟩))
            (.original (.row ⟨92105866079, 92643323332, (.direct 3393509060 4310786973), (.chord (.secant 1565978010337 273785895560 9635167323 45001477591) 3393555298 10180665226)⟩))))
        (.cut 3 (1/32)
          (.cut 0 (99/544)
            (.cut 1 (167/1600)
              (.cut 2 (1/16)
                (.original (.row ⟨92643323331, 92910789338, (.direct 1131165907 1736739763), (.chord .universal 0 3393555298)⟩))
                (.covered))
              (.cut 3 (1/64)
                (.original (.row ⟨92910789337, 93177423805, (.direct 377054043 822134522), (.chord .universal 0 10180665226)⟩))
                (.cut 2 (1/16)
                  (.original (.row ⟨92910789337, 93177423805, (.direct 1131165907 1740864635), (.chord .universal 0 3393555298)⟩))
                  (.covered))))
            (.cut 1 (167/1600)
              (.cut 3 (1/64)
                (.original (.row ⟨92643323331, 92910789338, (.direct 377054043 865090046), (.chord .universal 0 10180665226)⟩))
                (.cut 2 (1/16)
                  (.original (.row ⟨92643323331, 92910789338, (.direct 1131165907 1796421783), (.chord .universal 0 3393555298)⟩))
                  (.covered)))
              (.cut 3 (1/64)
                (.original (.row ⟨92910789337, 93177423805, (.direct 377054043 868626574), (.chord .universal 0 10180665226)⟩))
                (.cut 2 (1/16)
                  (.original (.row ⟨92910789337, 93177423805, (.direct 1131165907 1800978242), (.chord .universal 0 3393555298)⟩))
                  (.covered)))))
          (.cut 2 (1/16)
            (.original (.row ⟨92643323331, 93177423805, (.direct 3393509060 4322965602), (.variance 1045326832235)⟩))
            (.original (.row ⟨92643323331, 93177423805, (.direct 3393509060 4322965602), (.chord (.secant 1567693891011 274687751356 9748095250 45200665796) 3393555298 10180665226)⟩))))))

set_option maxRecDepth 16000 in
theorem CutMid2H1NegRestPart3_ok : CutMid2H1NegRestPart3Tree.ok CutMid2H1NegRestPart3Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
