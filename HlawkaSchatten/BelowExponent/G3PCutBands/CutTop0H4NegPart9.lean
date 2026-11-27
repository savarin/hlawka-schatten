/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H4NegPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H4NegPart9Box : Box := ((⟨![9/34, 3/20, 0, -8], ![45/136, 4/25, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop0H4NegPart9Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨110576703734, 114055813620, .zero, (.variance 308822662119)⟩))
        (.row ⟨110576703734, 114055813620, .zero, (.variance 308822662119)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨110576703734, 114055813620, (.direct 391506126583 387941774077), (.variance 251165064859)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 593382169971 583009540802), (.variance 225753544360)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 391506126583 387941774077), (.variance 251165064859)⟩))
        (.row ⟨110576703734, 114055813620, (.direct 391506126583 387941774077), (.variance 251165064859)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨110576703734, 114055813620, (.direct 824633666698 805912688135), (.variance 207402716939)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1937206444257), (.variance 164845380717)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3395901229368), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (5)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 805912688135), (.variance 207402716939)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3395901229368), (.variance 142312101052)⟩)))
      (.row ⟨110576703734, 114055813620, (.direct 824633666698 805912688135), (.variance 207402716939)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H4NegPart9_checked : CutTop0H4NegPart9Tree.commonOK CutTop0H4NegPart9Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
