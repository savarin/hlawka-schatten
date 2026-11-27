/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H1NegPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H1NegPart9Box : Box := ((⟨![9/136, 3/20, 0, -8], ![9/68, 4/25, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop0H1NegPart9Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨110576703734, 114055813620, .zero, (.variance 309508094644)⟩))
        (.row ⟨110576703734, 114055813620, .zero, (.variance 309508094644)⟩))
      (.row ⟨110576703734, 114055813620, (.direct 391506126583 390079199168), (.variance 250803954860)⟩))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 817127919083), (.variance 206653501759)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3472301378325), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (5)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 817127919083), (.variance 206653501759)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3472301378325), (.variance 141485419262)⟩)))
      (.row ⟨110576703734, 114055813620, (.direct 824633666698 817127919083), (.variance 206653501759)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H1NegPart9_checked : CutTop0H1NegPart9Tree.commonOK CutTop0H1NegPart9Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
