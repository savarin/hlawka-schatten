/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H4NegPart27`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H4NegPart27Box : Box := (((((((((⟨![9/34, 9/50, 0, -8], ![45/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 3 (0)).upperChild 2 (5/16)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutTop3H4NegPart27Tree : CertTree :=
  .cut 3 (3/16)
    (.cut 2 (13/32)
      (.cut 3 (5/32)
        (.row ⟨120689819474, 123862991200, (.direct 14500097491 19041523110), (.chord (.secant 1049816801903 47213602984 1244907918 55417882564) 43500686443 65931360876)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 24175991139), (.chord (.secant 1119608060512 70977634819 8087787730 74548675105) 43500686443 65931360876)⟩))
      (.row ⟨120689819474, 123862991200, (.direct 19358451269 24175991139), (.chord (.secant 1005324292390 33757545326 1357925622 39877040175) 65931360876 91625974997)⟩))
    (.cut 2 (13/32)
      (.cut 3 (7/32)
        (.row ⟨120689819474, 123862991200, (.direct 24716051037 29749150056), (.chord (.secant 1191043339732 98135338471 18629915786 95694953426) 43500686443 65931360876)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 30541785600 35737713343), (.chord (.secant 1264096217991 128407989865 32090644565 118728407304) 43500686443 65931360876)⟩))
      (.row ⟨120689819474, 123862991200, (.direct 30541785600 35737713343), (.chord (.secant 1111717852693 68144415979 5696652293 68859207999) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop3H4NegPart27_checked : CutTop3H4NegPart27Tree.commonOK CutTop3H4NegPart27Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
