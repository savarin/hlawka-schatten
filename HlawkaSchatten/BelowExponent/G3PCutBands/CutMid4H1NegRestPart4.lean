/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H1NegRestPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H1NegRestPart4Box : Box := (((((((((⟨![9/68, 13/100, 0, -8], ![9/34, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutMid4H1NegRestPart4Tree : RatioRemainder :=
  .cut 1 (7/50)
    (.cut 3 (3/32)
      (.cut 0 (27/136)
        (.cut 2 (1/16)
          (.original (.row ⟨103236350715, 106974752992, (.direct 6452795533 7991467677), (.variance 823363014925)⟩))
          (.cut 2 (3/32)
            (.original (.row ⟨103236350715, 106974752992, (.direct 6452795533 7991467677), (.chord (.secant 2079010917775 570012048034 109700443844 177432727190) 3393555298 6452870597)⟩))
            (.original (.row ⟨103236350715, 106974752992, (.direct 6452795533 7991467677), (.chord (.secant 1578088756821 280166737819 56969806503 112463064464) 6452870597 10180665226)⟩))))
        (.cut 1 (27/200)
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨103236350715, 105123556200, (.direct 4833349683 6676730711), (.variance 803488979954)⟩))
              (.original (.row ⟨103236350715, 105123556200, (.direct 4833349683 6676730711), (.chord (.secant 1853714916531 434066661723 49445736998 123462025832) 3393555298 10180665226)⟩)))
            (.cut 2 (1/16)
              (.original (.row ⟨103236350715, 105123556200, (.direct 6452795533 8447406262), (.variance 743836675426)⟩))
              (.original (.row ⟨103236350715, 105123556200, (.direct 6452795533 8447406262), (.chord (.secant 2074401168957 567154180475 80859217457 165757763846) 3393555298 10180665226)⟩))))
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨105123556199, 106974752992, (.direct 4833349683 6754613530), (.variance 801141613964)⟩))
              (.original (.row ⟨105123556199, 106974752992, (.direct 4833349683 6754613530), (.chord (.secant 1863643275021 439885300392 50436929626 124849199255) 3393555298 10180665226)⟩)))
            (.original (.row ⟨105123556199, 106974752992, (.direct 6452795533 8530885779), (.variance 742060628221)⟩)))))
      (.cut 0 (27/136)
        (.cut 1 (27/200)
          (.cut 3 (7/64)
            (.cut 0 (45/272)
              (.original (.row ⟨103236350715, 105123556200, (.direct 8238656156 9547962877), (.variance 708682755735)⟩))
              (.original (.row ⟨103236350715, 105123556200, (.direct 8238656156 9818277867), (.variance 702762111749)⟩)))
            (.original (.row ⟨103236350715, 105123556200, (.direct 10180561190 11850984853), (.variance 668347416130)⟩)))
          (.cut 3 (7/64)
            (.cut 0 (45/272)
              (.original (.row ⟨105123556199, 106974752992, (.direct 8238656156 9601566795), (.variance 707694224406)⟩))
              (.original (.row ⟨105123556199, 106974752992, (.direct 8238656156 9883280794), (.variance 701561932738)⟩)))
            (.original (.row ⟨105123556199, 106974752992, (.direct 10180561190 11919429383), (.variance 667551586100)⟩))))
        (.cut 1 (27/200)
          (.cut 3 (7/64)
            (.original (.row ⟨103236350715, 105123556200, (.direct 8238656156 10367213274), (.variance 697006785546)⟩))
            (.original (.row ⟨103236350715, 105123556200, (.direct 10180561190 12428334866), (.variance 658912217385)⟩)))
          (.original (.row ⟨105123556199, 106974752992, (.direct 10180561190 12521239524), (.variance 695607107204)⟩)))))
    (.cut 3 (3/32)
      (.cut 0 (27/136)
        (.cut 2 (1/16)
          (.original (.row ⟨106974752991, 110576703735, (.direct 6452795533 8115270438), (.variance 819959225889)⟩))
          (.cut 2 (3/32)
            (.original (.row ⟨106974752991, 110576703735, (.direct 6452795533 8115270438), (.chord (.secant 2094413745302 579582562274 112072108533 180262013483) 3393555298 6452870597)⟩))
            (.original (.row ⟨106974752991, 110576703735, (.direct 6452795533 8115270438), (.chord (.secant 1587361316564 285076449419 58367203804 114256365012) 6452870597 10180665226)⟩))))
        (.cut 1 (29/200)
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨106974752991, 108791878640, (.direct 4833349683 6833251747), (.variance 798805032175)⟩))
              (.original (.row ⟨106974752991, 108791878640, (.direct 4833349683 6833251747), (.chord (.secant 1873644873624 445764083388 51440751585 126249588558) 3393555298 10180665226)⟩)))
            (.original (.row ⟨106974752991, 108791878640, (.direct 6452795533 8615120358), (.variance 740289523602)⟩)))
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨108791878639, 110576703735, (.direct 4833349683 6912653188), (.variance 796479112872)⟩))
              (.original (.row ⟨108791878639, 110576703735, (.direct 4833349683 6912653188), (.chord (.secant 1883720438569 451703631374 52457326210 127663330320) 3393555298 10180665226)⟩)))
            (.original (.row ⟨108791878639, 110576703735, (.direct 6452795533 8700117807), (.variance 738523316768)⟩)))))
      (.cut 0 (27/136)
        (.cut 1 (29/200)
          (.cut 3 (7/64)
            (.original (.row ⟨106974752991, 108791878640, (.direct 8238656156 9948793593), (.variance 706705101642)⟩))
            (.original (.row ⟨106974752991, 108791878640, (.direct 10180561190 11988389426), (.variance 666754725026)⟩)))
          (.cut 3 (7/64)
            (.cut 0 (45/272)
              (.original (.row ⟨108791878639, 110576703735, (.direct 8238656156 9709980250), (.variance 705715382259)⟩))
              (.original (.row ⟨108791878639, 110576703735, (.direct 8238656156 10014821419), (.variance 699163255117)⟩)))
            (.original (.row ⟨108791878639, 110576703735, (.direct 10180561190 12057870130), (.variance 665956828165)⟩))))
        (.cut 1 (29/200)
          (.original (.row ⟨106974752991, 108791878640, (.direct 10180561190 12614902194), (.variance 694209517392)⟩))
          (.cut 3 (7/64)
            (.original (.row ⟨108791878639, 110576703735, (.direct 8238656156 10634867810), (.variance 692813997888)⟩))
            (.original (.row ⟨108791878639, 110576703735, (.direct 10180561190 12709330604), (.variance 655505331615)⟩))))))

set_option maxRecDepth 16000 in
theorem CutMid4H1NegRestPart4_ok : CutMid4H1NegRestPart4Tree.ok CutMid4H1NegRestPart4Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
