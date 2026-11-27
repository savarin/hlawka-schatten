/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H5NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H5NegRestPart1Box : Box := ((⟨![45/136, 3/20, 0, -8], ![27/68, 4/25, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop0H5NegRestPart1Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨110576703734, 114055813620, .zero, (.variance 308595331847)⟩)))
        (.original (.row ⟨110576703734, 114055813620, .zero, (.variance 308595331847)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨110576703734, 114055813620, (.direct 391506126583 387230262640), (.variance 251285829420)⟩))
            (.original (.row ⟨110576703734, 114055813620, (.direct 593382169971 580942844104), (.variance 225963569113)⟩)))
          (.original (.row ⟨110576703734, 114055813620, (.direct 391506126583 387230262640), (.variance 251285829420)⟩)))
        (.original (.row ⟨110576703734, 114055813620, (.direct 391506126583 387230262640), (.variance 251285829420)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 802187002831), (.variance 207654521677)⟩))
            (.original (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1924337031804), (.variance 165133350700)⟩)))
          (.original (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3370574147296), (.variance 142591345294)⟩)))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 802187002831), (.variance 207654521677)⟩))
            (.original (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1924337031804), (.variance 165133350700)⟩)))
          (.original (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3370574147296), (.variance 142591345294)⟩))))
      (.original (.row ⟨110576703734, 114055813620, (.direct 824633666698 802187002831), (.variance 207654521677)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop0H5NegRestPart1_ok : CutTop0H5NegRestPart1Tree.ok CutTop0H5NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
