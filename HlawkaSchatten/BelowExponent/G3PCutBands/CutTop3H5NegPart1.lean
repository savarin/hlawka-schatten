/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H5NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H5NegPart1Box : Box := ((((((⟨![45/136, 9/50, 0, -8], ![27/68, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop3H5NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨120689819474, 123862991200, (.direct 0 1785585184), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.cut 1 (37/200)
            (.row ⟨120689819474, 122287555846, (.direct 1131165907 4103374951), (.chord .universal 0 10180665226)⟩)
            (.row ⟨122287555845, 123862991200, (.direct 1131165907 4211979863), (.chord .universal 0 10180665226)⟩))
          (.row ⟨120689819474, 123862991200, (.direct 3393509060 7327159114), (.variance 866155916076)⟩))
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 15275518371), (.variance 736056136948)⟩))
      (.cut 3 (3/16)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 25186201612), (.variance 598105938904)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 30541785600 36812648456), (.variance 521156964382)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop3H5NegPart1_checked : CutTop3H5NegPart1Tree.commonOK CutTop3H5NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
