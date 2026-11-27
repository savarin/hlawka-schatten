/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H0NegPart25`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H0NegPart25Box : Box := ((⟨![0, 13/100, 0, -8], ![9/68, 3/20, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid4H0NegPart25Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨103236350715, 110576703735, .zero, (.variance 309737727641)⟩))
        (.row ⟨103236350715, 110576703735, .zero, (.variance 309737727641)⟩))
      (.row ⟨103236350715, 110576703735, (.direct 391506126583 390175581571), (.variance 250787730274)⟩))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.row ⟨103236350715, 110576703735, (.direct 824633666698 817634455217), (.variance 206619970078)⟩)
          (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3475757576498), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (5)
          (.row ⟨103236350715, 110576703735, (.direct 824633666698 817634455217), (.variance 206619970078)⟩)
          (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3475757576498), (.variance 141448565462)⟩)))
      (.row ⟨103236350715, 110576703735, (.direct 824633666698 817634455217), (.variance 206619970078)⟩))

set_option maxRecDepth 16000 in
theorem CutMid4H0NegPart25_checked : CutMid4H0NegPart25Tree.commonOK CutMid4H0NegPart25Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
