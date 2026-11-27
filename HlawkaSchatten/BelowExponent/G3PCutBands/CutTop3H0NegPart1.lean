/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H0NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H0NegPart1Box : Box := ((((((⟨![0, 9/50, 0, -8], ![9/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop3H0NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨120689819474, 123862991200, (.direct 0 104337421), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 1 (37/200)
          (.cut 0 (9/272)
            (.cut 1 (73/400)
              (.row ⟨120689819474, 121491533044, (.direct 3393509060 3665493173), (.chord .universal 0 10180665226)⟩)
              (.row ⟨121491533043, 122287555846, (.direct 3393509060 3669657111), (.chord .universal 0 10180665226)⟩))
            (.cut 1 (73/400)
              (.row ⟨120689819474, 121491533044, (.direct 3393509060 3945090364), (.chord .universal 0 10180665226)⟩)
              (.row ⟨121491533043, 122287555846, (.direct 3393509060 3953648897), (.chord .universal 0 10180665226)⟩)))
          (.cut 0 (9/272)
            (.row ⟨122287555845, 123862991200, (.direct 3393509060 3678024764), (.chord .universal 0 10180665226)⟩)
            (.row ⟨122287555845, 123862991200, (.direct 3393509060 3970857560), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (3/32)
          (.cut 2 (1/16)
            (.row ⟨120689819474, 123862991200, (.direct 6452795533 7153032458), (.variance 868750156237)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 6452795533 7153032458), (.chord (.secant 2094113152216 579395476887 73163544754 91625662891) 3393555298 10180665226)⟩))
          (.cut 3 (7/64)
            (.cut 2 (1/16)
              (.row ⟨120689819474, 123862991200, (.direct 8238656156 8989517051), (.variance 734193276773)⟩)
              (.row ⟨120689819474, 123862991200, (.direct 8238656156 8989517051), (.chord (.secant 2327530846108 728150689878 150498559827 174227225485) 3393555298 10180665226)⟩))
            (.cut 1 (37/200)
              (.row ⟨120689819474, 122287555846, (.direct 10180561190 10953008612), (.variance 688691889909)⟩)
              (.row ⟨122287555845, 123862991200, (.direct 10180561190 10976393387), (.variance 688691889909)⟩)))))
      (.cut 3 (3/16)
        (.cut 3 (5/32)
          (.cut 3 (9/64)
            (.cut 1 (37/200)
              (.row ⟨120689819474, 122287555846, (.direct 12270063068 13081449549), (.variance 651562574406)⟩)
              (.row ⟨122287555845, 123862991200, (.direct 12270063068 13105971251), (.variance 651562574406)⟩))
            (.row ⟨120689819474, 123862991200, (.direct 14500097491 15371757185), (.variance 620477318811)⟩))
          (.cut 3 (11/64)
            (.row ⟨120689819474, 123862991200, (.direct 16864636136 17768167520), (.variance 593929411221)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 19358451269 20290330076), (.variance 570893780246)⟩)))
        (.cut 3 (7/32)
          (.cut 3 (13/64)
            (.row ⟨120689819474, 123862991200, (.direct 21976949588 22933942007), (.variance 550644921433)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 24716051037 25695164784), (.variance 532652607245)⟩))
          (.cut 3 (15/64)
            (.row ⟨120689819474, 123862991200, (.direct 27572097984 28570544657), (.variance 516518883525)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 30541785600 31556951123), (.variance 501938304662)⟩)))))

set_option maxRecDepth 16000 in
theorem CutTop3H0NegPart1_checked : CutTop3H0NegPart1Tree.commonOK CutTop3H0NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
