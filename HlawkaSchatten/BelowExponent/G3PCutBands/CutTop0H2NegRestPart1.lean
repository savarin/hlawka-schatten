/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H2NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H2NegRestPart1Box : Box := ((⟨![9/68, 3/20, 0, -8], ![27/136, 4/25, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop0H2NegRestPart1Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨110576703734, 114055813620, .zero, (.variance 309279041049)⟩)))
        (.original (.row ⟨110576703734, 114055813620, .zero, (.variance 309279041049)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨110576703734, 114055813620, (.direct 391506126583 389366242572), (.variance 250924128129)⟩))
            (.original (.row ⟨110576703734, 114055813620, (.direct 593382169971 587151053993), (.variance 225335483495)⟩)))
          (.original (.row ⟨110576703734, 114055813620, (.direct 391506126583 389366242572), (.variance 250924128129)⟩)))
        (.original (.row ⟨110576703734, 114055813620, (.direct 391506126583 389366242572), (.variance 250924128129)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 813383153944), (.variance 206902214225)⟩))
            (.original (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1963040108913), (.variance 164274538582)⟩)))
          (.original (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3446764980694), (.chord .universal 0 10180665226)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 813383153944), (.variance 206902214225)⟩))
          (.original (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3446764980694), (.variance 141759158819)⟩))))
      (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 813383153944), (.variance 206902214225)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop0H2NegRestPart1_ok : CutTop0H2NegRestPart1Tree.ok CutTop0H2NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
