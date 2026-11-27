/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H0NegPart10`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H0NegPart10Box : Box := ((⟨![0, 3/20, 0, -8], ![9/136, 4/25, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop0H0NegPart10Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨110576703734, 114055813620, .zero, (.variance 309737727641)⟩))
        (.row ⟨110576703734, 114055813620, .zero, (.variance 309737727641)⟩))
      (.row ⟨110576703734, 114055813620, (.direct 391506126583 390792637022), (.variance 250683977592)⟩))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 820879028854), (.variance 206405805678)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3497907277678), (.chord .universal 0 10180665226)⟩))
        (.row ⟨110576703734, 114055813620, (.direct 824633666698 820879028854), (.variance 206405805678)⟩))
      (.row ⟨110576703734, 114055813620, (.direct 824633666698 820879028854), (.variance 206405805678)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H0NegPart10_checked : CutTop0H0NegPart10Tree.commonOK CutTop0H0NegPart10Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
