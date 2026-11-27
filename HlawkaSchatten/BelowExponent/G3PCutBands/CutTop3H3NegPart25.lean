/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H3NegPart25`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H3NegPart25Box : Box := ((⟨![27/136, 9/50, 0, -8], ![9/34, 19/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop3H3NegPart25Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨120689819474, 123862991200, .zero, (.variance 308900234789)⟩))
        (.row ⟨120689819474, 123862991200, .zero, (.variance 308900234789)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨120689819474, 123862991200, (.direct 391506126583 388063683499), (.variance 251144401265)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 593382169971 583363777061), (.variance 225717639977)⟩))
          (.row ⟨120689819474, 123862991200, (.direct 391506126583 388063683499), (.variance 251144401265)⟩))
        (.row ⟨120689819474, 123862991200, (.direct 391506126583 388063683499), (.variance 251144401265)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨120689819474, 123862991200, (.direct 824633666698 806551427834), (.variance 207359694478)⟩)
            (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1939413772012), (.variance 164796231385)⟩))
          (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3400246032600), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (5)
          (.row ⟨120689819474, 123862991200, (.direct 824633666698 806551427834), (.variance 207359694478)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3400246032600), (.variance 142264461409)⟩)))
      (.row ⟨120689819474, 123862991200, (.direct 824633666698 806551427834), (.variance 207359694478)⟩))

set_option maxRecDepth 16000 in
theorem CutTop3H3NegPart25_checked : CutTop3H3NegPart25Tree.commonOK CutTop3H3NegPart25Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
