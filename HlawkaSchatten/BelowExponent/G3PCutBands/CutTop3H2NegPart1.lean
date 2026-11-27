/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H2NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H2NegPart1Box : Box := ((((((⟨![9/68, 9/50, 0, -8], ![27/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop3H2NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨120689819474, 123862991200, (.direct 0 595195101), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 1 (37/200)
          (.cut 0 (45/272)
            (.cut 1 (73/400)
              (.cut 3 (1/32)
                (.row ⟨120689819474, 121491533044, (.direct 1131165907 2185111910), (.chord .universal 0 10180665226)⟩)
                (.row ⟨120689819474, 121491533044, (.direct 3393509060 4828421367), (.chord .universal 0 10180665226)⟩))
              (.cut 3 (1/32)
                (.row ⟨121491533043, 122287555846, (.direct 1131165907 2202909438), (.chord .universal 0 10180665226)⟩)
                (.row ⟨121491533043, 122287555846, (.direct 3393509060 4851485284), (.chord .universal 0 10180665226)⟩)))
            (.cut 1 (73/400)
              (.cut 3 (1/32)
                (.row ⟨120689819474, 121491533044, (.direct 1131165907 2425206031), (.chord .universal 0 10180665226)⟩)
                (.cut 2 (1/16)
                  (.row ⟨120689819474, 121491533044, (.direct 3393509060 5137281224), (.variance 976972298109)⟩)
                  (.row ⟨120689819474, 121491533044, (.direct 3393509060 5137281224), (.chord (.secant 1680152365084 335309285423 17871456469 58519950495) 3393555298 10180665226)⟩)))
              (.cut 3 (1/32)
                (.row ⟨121491533043, 122287555846, (.direct 1131165907 2447404902), (.chord .universal 0 10180665226)⟩)
                (.row ⟨121491533043, 122287555846, (.direct 3393509060 5165602413), (.chord .universal 0 10180665226)⟩))))
          (.cut 0 (45/272)
            (.cut 1 (3/16)
              (.row ⟨122287555845, 123078004368, (.direct 3393509060 4874653531), (.chord .universal 0 10180665226)⟩)
              (.row ⟨123078004367, 123862991200, (.direct 3393509060 4897926659), (.chord .universal 0 10180665226)⟩))
            (.cut 1 (3/16)
              (.cut 3 (1/32)
                (.row ⟨122287555845, 123078004368, (.direct 1131165907 2469739883), (.chord .universal 0 10180665226)⟩)
                (.row ⟨122287555845, 123078004368, (.direct 3393509060 5194059390), (.chord .universal 0 10180665226)⟩))
              (.row ⟨123078004367, 123862991200, (.direct 3393509060 5222652875), (.chord .universal 0 10180665226)⟩))))
        (.cut 3 (3/32)
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.row ⟨120689819474, 123862991200, (.direct 4833349683 6848543609), (.variance 806456839205)⟩)
              (.row ⟨120689819474, 123862991200, (.direct 4833349683 6848543609), (.chord (.secant 1934492861789 481891487366 64240335567 121735889844) 3393555298 10180665226)⟩))
            (.row ⟨120689819474, 123862991200, (.direct 6452795533 8631494191), (.variance 746077554034)⟩))
          (.row ⟨120689819474, 123862991200, (.direct 10180561190 12633099205), (.variance 698770199276)⟩)))
      (.cut 3 (3/16)
        (.cut 3 (5/32)
          (.row ⟨120689819474, 123862991200, (.direct 14500097491 17170434929), (.variance 628280461587)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 19358451269 22201774806), (.variance 577329926958)⟩))
        (.cut 3 (7/32)
          (.row ⟨120689819474, 123862991200, (.direct 24716051037 27694772853), (.variance 538179200147)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 30541785600 33623345238), (.variance 506816466504)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop3H2NegPart1_checked : CutTop3H2NegPart1Tree.commonOK CutTop3H2NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
