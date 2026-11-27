/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H3NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H3NegPart1Box : Box := ((((((⟨![27/136, 9/50, 0, -8], ![9/34, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop3H3NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨120689819474, 123862991200, (.direct 0 939036661), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 1 (37/200)
          (.cut 0 (63/272)
            (.cut 1 (73/400)
              (.cut 3 (1/32)
                (.row ⟨120689819474, 121491533044, (.direct 1131165907 2674413597), (.chord .universal 0 10180665226)⟩)
                (.cut 2 (1/16)
                  (.row ⟨120689819474, 121491533044, (.direct 3393509060 5453152154), (.variance 950913916464)⟩)
                  (.row ⟨120689819474, 121491533044, (.direct 3393509060 5453152154), (.chord (.secant 1694408206868 343195482807 16659473077 64884546424) 3393555298 10180665226)⟩)))
              (.cut 3 (1/32)
                (.row ⟨121491533043, 122287555846, (.direct 1131165907 2701268676), (.chord .universal 0 10180665226)⟩)
                (.cut 2 (1/16)
                  (.row ⟨121491533043, 122287555846, (.direct 3393509060 5486933494), (.variance 948640924204)⟩)
                  (.row ⟨121491533043, 122287555846, (.direct 3393509060 5486933494), (.chord (.secant 1698899550642 345688931287 17020966096 65480258686) 3393555298 10180665226)⟩))))
            (.cut 3 (1/32)
              (.row ⟨120689819474, 122287555846, (.direct 1131165907 2964261531), (.chord .universal 0 10180665226)⟩)
              (.cut 2 (1/16)
                (.row ⟨120689819474, 122287555846, (.direct 3393509060 5815365388), (.variance 927082535354)⟩)
                (.row ⟨120689819474, 122287555846, (.direct 3393509060 5815365388), (.chord (.secant 1713857708102 354023475028 15479194200 71488425625) 3393555298 10180665226)⟩))))
          (.cut 0 (63/272)
            (.cut 1 (3/16)
              (.cut 3 (1/32)
                (.row ⟨122287555845, 123078004368, (.direct 1131165907 2728297146), (.chord .universal 0 10180665226)⟩)
                (.row ⟨122287555845, 123078004368, (.direct 3393509060 5520885278), (.chord .universal 0 10180665226)⟩))
              (.cut 3 (1/32)
                (.row ⟨123078004367, 123862991200, (.direct 1131165907 2755499879), (.chord .universal 0 10180665226)⟩)
                (.row ⟨123078004367, 123862991200, (.direct 3393509060 5555008405), (.chord .universal 0 10180665226)⟩)))
            (.cut 3 (1/32)
              (.row ⟨122287555845, 123862991200, (.direct 1131165907 3028420369), (.chord .universal 0 10180665226)⟩)
              (.cut 2 (1/16)
                (.row ⟨122287555845, 123862991200, (.direct 3393509060 5894870944), (.variance 922235455893)⟩)
                (.row ⟨122287555845, 123862991200, (.direct 3393509060 5894870944), (.chord (.secant 1724216152960 359822050262 16305937072 72933939835) 3393555298 10180665226)⟩)))))
        (.cut 3 (3/32)
          (.cut 3 (5/64)
            (.row ⟨120689819474, 123862991200, (.direct 4833349683 7576314659), (.variance 780486352393)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 6452795533 9408532105), (.variance 726293326071)⟩))
          (.row ⟨120689819474, 123862991200, (.direct 10180561190 13493285519), (.variance 683101815647)⟩)))
      (.cut 3 (3/16)
        (.cut 3 (5/32)
          (.row ⟨120689819474, 123862991200, (.direct 14500097491 18097052962), (.variance 617651011304)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 19358451269 23181125599), (.variance 569600391886)⟩))
        (.row ⟨120689819474, 123862991200, (.direct 30541785600 34674581032), (.variance 532295757829)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H3NegPart1_checked : CutTop3H3NegPart1Tree.commonOK CutTop3H3NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
