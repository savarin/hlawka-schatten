/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H7NegPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H7NegPart9Box : Box := ((⟨![63/136, 3/20, 0, -8], ![9/17, 4/25, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop0H7NegPart9Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨110576703734, 114055813620, .zero, (.variance 308142377461)⟩))
        (.row ⟨110576703734, 114055813620, .zero, (.variance 308142377461)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.row ⟨110576703734, 114055813620, (.direct 391506126583 385808686546), (.variance 251527953703)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 488587506629 477782935957), (.variance 237832224538)⟩))
            (.row ⟨110576703734, 114055813620, (.direct 593382169971 576817583100), (.variance 226385625275)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 391506126583 385808686546), (.variance 251527953703)⟩))
        (.row ⟨110576703734, 114055813620, (.direct 391506126583 385808686546), (.variance 251527953703)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.row ⟨110576703734, 114055813620, (.direct 824633666698 794754766079), (.variance 208161274693)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 1366046989981 1303170300422), (.variance 182878104439)⟩))
            (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1898693322940), (.variance 165714475522)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3320130256209), (.variance 143155486480)⟩))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨110576703734, 114055813620, (.direct 824633666698 794754766079), (.variance 208161274693)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1898693322940), (.variance 165714475522)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3320130256209), (.variance 143155486480)⟩)))
      (.row ⟨110576703734, 114055813620, (.direct 824633666698 794754766079), (.variance 208161274693)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H7NegPart9_checked : CutTop0H7NegPart9Tree.commonOK CutTop0H7NegPart9Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
