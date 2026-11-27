/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H0NegPart10`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H0NegPart10Box : Box := ((⟨![0, 4/25, 0, -8], ![9/136, 17/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop1H0NegPart10Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨114055813619, 117423580140, .zero, (.variance 309737727641)⟩))
        (.row ⟨114055813619, 117423580140, .zero, (.variance 309737727641)⟩))
      (.row ⟨114055813619, 117423580140, (.direct 391506126583 390743889619), (.variance 250692166535)⟩))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 820622603777), (.variance 206422692612)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3496156032023), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (5)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 820622603777), (.variance 206422692612)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3496156032023), (.variance 141231992435)⟩)))
      (.row ⟨114055813619, 117423580140, (.direct 824633666698 820622603777), (.variance 206422692612)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H0NegPart10_checked : CutTop1H0NegPart10Tree.commonOK CutTop1H0NegPart10Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
