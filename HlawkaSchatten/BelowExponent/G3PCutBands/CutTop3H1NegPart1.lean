/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H1NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H1NegPart1Box : Box := ((((((⟨![9/136, 9/50, 0, -8], ![9/68, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop3H1NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨120689819474, 123862991200, (.direct 0 313012241), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 1 (37/200)
          (.cut 0 (27/272)
            (.cut 1 (73/400)
              (.row ⟨120689819474, 121491533044, (.direct 3393509060 4232200773), (.chord .universal 0 10180665226)⟩)
              (.row ⟨121491533043, 122287555846, (.direct 3393509060 4245378067), (.chord .universal 0 10180665226)⟩))
            (.cut 1 (73/400)
              (.cut 3 (1/32)
                (.row ⟨120689819474, 121491533044, (.direct 1131165907 1954383707), (.chord .universal 0 10180665226)⟩)
                (.row ⟨120689819474, 121491533044, (.direct 3393509060 4526687390), (.chord .universal 0 10180665226)⟩))
              (.row ⟨121491533043, 122287555846, (.direct 3393509060 4544701644), (.chord .universal 0 10180665226)⟩)))
          (.cut 0 (27/272)
            (.row ⟨122287555845, 123862991200, (.direct 3393509060 4271887498), (.chord .universal 0 10180665226)⟩)
            (.cut 1 (3/16)
              (.row ⟨122287555845, 123078004368, (.direct 3393509060 4562792095), (.chord .universal 0 10180665226)⟩)
              (.row ⟨123078004367, 123862991200, (.direct 3393509060 4580959139), (.chord .universal 0 10180665226)⟩))))
        (.cut 3 (3/32)
          (.cut 2 (1/16)
            (.row ⟨120689819474, 123862991200, (.direct 6452795533 7879459474), (.variance 835631601062)⟩)
            (.cut 2 (3/32)
              (.row ⟨120689819474, 123862991200, (.direct 6452795533 7879459474), (.chord (.secant 2126050777178 599341604989 122249175450 167688518295) 3393555298 6452870597)⟩)
              (.row ⟨120689819474, 123862991200, (.direct 6452795533 7879459474), (.chord (.secant 1624867778893 305144588439 68648419004 106286844269) 6452870597 10180665226)⟩)))
          (.cut 3 (7/64)
            (.row ⟨120689819474, 123862991200, (.direct 8238656156 9764180863), (.variance 715735779956)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 10180561190 11794007410), (.variance 674009418277)⟩))))
      (.cut 3 (3/16)
        (.cut 3 (5/32)
          (.cut 3 (9/64)
            (.row ⟨120689819474, 123862991200, (.direct 12270063068 13961914014), (.variance 639560626480)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 14500097491 16261916480), (.variance 610459694140)⟩))
          (.row ⟨120689819474, 123862991200, (.direct 19358451269 21238115156), (.variance 585429186538)⟩))
        (.cut 3 (7/32)
          (.row ⟨120689819474, 123862991200, (.direct 24716051037 26688056507), (.variance 544290429484)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 30541785600 32584102264), (.variance 511589273113)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop3H1NegPart1_checked : CutTop3H1NegPart1Tree.commonOK CutTop3H1NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
