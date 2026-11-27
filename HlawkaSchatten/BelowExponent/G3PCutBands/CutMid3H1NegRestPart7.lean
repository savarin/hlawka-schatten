/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H1NegRestPart7`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H1NegRestPart7Box : Box := (((((((((⟨![9/68, 11/100, 0, -8], ![9/34, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutMid3H1NegRestPart7Tree : RatioRemainder :=
  .cut 1 (3/25)
    (.cut 3 (3/32)
      (.cut 2 (1/16)
        (.original (.row ⟨95281442640, 99345187400, (.direct 6452795533 8201421464), (.variance 830205812341)⟩))
        (.cut 2 (3/32)
          (.original (.row ⟨95281442640, 99345187400, (.direct 6452795533 8201421464), (.chord (.secant 2105105597086 586245062666 85599566524 171912393999) 3393555298 6452870597)⟩))
          (.original (.row ⟨95281442640, 99345187400, (.direct 6452795533 8201421464), (.chord (.secant 1593794801161 288495102325 39291894842 108964084331) 6452870597 10180665226)⟩))))
      (.cut 0 (27/136)
        (.cut 1 (23/200)
          (.cut 3 (7/64)
            (.cut 2 (1/16)
              (.original (.row ⟨95281442640, 97336292160, (.direct 8238656156 9563264096), (.variance 712631069331)⟩))
              (.original (.row ⟨95281442640, 97336292160, (.direct 8238656156 9563264096), (.chord (.secant 2271474627535 691823251593 124698864169 195233144398) 3393555298 10180665226)⟩)))
            (.original (.row ⟨95281442640, 97336292160, (.direct 10180561190 11582261136), (.variance 671520519493)⟩)))
          (.cut 3 (7/64)
            (.cut 0 (45/272)
              (.original (.row ⟨97336292159, 99345187400, (.direct 8238656156 9389515228), (.variance 711644852501)⟩))
              (.original (.row ⟨97336292159, 99345187400, (.direct 8238656156 9626277771), (.variance 706366115498)⟩)))
            (.original (.row ⟨97336292159, 99345187400, (.direct 10180561190 11648693822), (.variance 670728766877)⟩))))
        (.cut 1 (23/200)
          (.cut 3 (7/64)
            (.original (.row ⟨95281442640, 97336292160, (.direct 8238656156 10020785566), (.variance 702626751547)⟩))
            (.original (.row ⟨95281442640, 97336292160, (.direct 10180561190 12064145115), (.variance 663463254936)⟩)))
          (.cut 3 (7/64)
            (.original (.row ⟨97336292159, 99345187400, (.direct 8238656156 10106295981), (.variance 701218535210)⟩))
            (.original (.row ⟨97336292159, 99345187400, (.direct 10180561190 12154093105), (.variance 662324556526)⟩))))))
    (.cut 3 (3/32)
      (.cut 0 (27/136)
        (.cut 2 (1/16)
          (.original (.row ⟨99345187399, 103236350716, (.direct 6452795533 7869681590), (.variance 826778476576)⟩))
          (.cut 2 (3/32)
            (.original (.row ⟨99345187399, 103236350716, (.direct 6452795533 7869681590), (.chord (.secant 2063814156810 560601890851 107372485416 174649829824) 3393555298 6452870597)⟩))
            (.original (.row ⟨99345187399, 103236350716, (.direct 6452795533 7869681590), (.chord (.secant 1568935113002 275340582828 55599613027 110699166841) 6452870597 10180665226)⟩))))
        (.cut 1 (1/8)
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨99345187399, 101311009181, (.direct 4833349683 6523200468), (.variance 808216560086)⟩))
              (.original (.row ⟨99345187399, 101311009181, (.direct 4833349683 6523200468), (.chord (.secant 1834075059856 422607375357 47500755375 120726789077) 3393555298 10180665226)⟩)))
            (.cut 2 (1/16)
              (.original (.row ⟨99345187399, 101311009181, (.direct 6452795533 8282681667), (.variance 747403778835)⟩))
              (.original (.row ⟨99345187399, 101311009181, (.direct 6452795533 8282681667), (.chord (.secant 2054272485129 554710099116 78561233692 162756912904) 3393555298 10180665226)⟩))))
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨101311009180, 103236350716, (.direct 4833349683 6599595565), (.variance 805847253590)⟩))
              (.original (.row ⟨101311009180, 103236350716, (.direct 4833349683 6599595565), (.chord (.secant 1843859080928 428307554869 48467052168 122087933469) 3393555298 10180665226)⟩)))
            (.cut 2 (1/16)
              (.original (.row ⟨101311009180, 103236350716, (.direct 6452795533 8364674095), (.variance 745617710424)⟩))
              (.original (.row ⟨101311009180, 103236350716, (.direct 6452795533 8364674095), (.chord (.secant 2064300862395 560902766972 79704105137 164250807990) 3393555298 10180665226)⟩))))))
      (.cut 0 (27/136)
        (.cut 1 (1/8)
          (.cut 3 (7/64)
            (.cut 0 (45/272)
              (.original (.row ⟨99345187399, 101311009181, (.direct 8238656156 9441940960), (.variance 710658064673)⟩))
              (.original (.row ⟨99345187399, 101311009181, (.direct 8238656156 9689781348), (.variance 705164194308)⟩)))
            (.original (.row ⟨99345187399, 101311009181, (.direct 10180561190 11715622062), (.variance 669936001858)⟩)))
          (.cut 3 (7/64)
            (.cut 0 (45/272)
              (.original (.row ⟨101311009180, 103236350716, (.direct 8238656156 9494755562), (.variance 709670700783)⟩))
              (.original (.row ⟨101311009180, 103236350716, (.direct 8238656156 9753779727), (.variance 703962862664)⟩)))
            (.original (.row ⟨101311009180, 103236350716, (.direct 10180561190 11783050753), (.variance 669142219823)⟩))))
        (.cut 1 (1/8)
          (.cut 3 (7/64)
            (.original (.row ⟨99345187399, 101311009181, (.direct 8238656156 10192532462), (.variance 699812481120)⟩))
            (.original (.row ⟨99345187399, 101311009181, (.direct 10180561190 12244769146), (.variance 661186489869)⟩)))
          (.cut 3 (7/64)
            (.original (.row ⟨101311009180, 103236350716, (.direct 8238656156 10279502399), (.variance 698408570722)⟩))
            (.original (.row ⟨101311009180, 103236350716, (.direct 10180561190 12336180585), (.variance 660049046357)⟩))))))

set_option maxRecDepth 16000 in
theorem CutMid3H1NegRestPart7_ok : CutMid3H1NegRestPart7Tree.geometryOK CutMid3H1NegPowerCache CutMid3H1NegRestPart7Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
