/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H1NegRestPart10`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H1NegRestPart10Box : Box := ((⟨![9/68, 13/100, 0, -8], ![9/34, 3/20, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid4H1NegRestPart10Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨103236350715, 110576703735, .zero, (.variance 309344309364)⟩)))
        (.original (.row ⟨103236350715, 110576703735, .zero, (.variance 309344309364)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨103236350715, 110576703735, (.direct 391506126583 388846280811), (.variance 251011946150)⟩))
            (.original (.row ⟨103236350715, 110576703735, (.direct 593382169971 585638707777), (.variance 225487713239)⟩)))
          (.original (.row ⟨103236350715, 110576703735, (.direct 391506126583 388846280811), (.variance 251011946150)⟩)))
        (.original (.row ⟨103236350715, 110576703735, (.direct 391506126583 388846280811), (.variance 251011946150)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 810654496084), (.variance 207084352661)⟩))
            (.original (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1953599679594), (.variance 164482037257)⟩)))
          (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3428174253099), (.variance 141960058499)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 810654496084), (.variance 207084352661)⟩))
          (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3428174253099), (.variance 141960058499)⟩))))
      (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 810654496084), (.variance 207084352661)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid4H1NegRestPart10_ok : CutMid4H1NegRestPart10Tree.ok CutMid4H1NegRestPart10Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
