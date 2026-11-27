/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H2NegPart10`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H2NegPart10Box : Box := ((⟨![9/68, 3/20, 0, -8], ![27/136, 4/25, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop0H2NegPart10Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨110576703734, 114055813620, .zero, (.variance 309279041049)⟩))
        (.row ⟨110576703734, 114055813620, .zero, (.variance 309279041049)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨110576703734, 114055813620, (.direct 391506126583 389366242572), (.variance 250924128129)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 593382169971 587151053993), (.variance 225335483495)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 391506126583 389366242572), (.variance 250924128129)⟩))
        (.row ⟨110576703734, 114055813620, (.direct 391506126583 389366242572), (.variance 250924128129)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨110576703734, 114055813620, (.direct 824633666698 813383153944), (.variance 206902214225)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1963040108913), (.variance 164274538582)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3446764980694), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (5)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 813383153944), (.variance 206902214225)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3446764980694), (.variance 141759158819)⟩)))
      (.row ⟨110576703734, 114055813620, (.direct 824633666698 813383153944), (.variance 206902214225)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H2NegPart10_checked : CutTop0H2NegPart10Tree.commonOK CutTop0H2NegPart10Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
