/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H3NegPart10`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H3NegPart10Box : Box := ((⟨![27/136, 3/20, 0, -8], ![9/34, 4/25, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop0H3NegPart10Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨110576703734, 114055813620, .zero, (.variance 309050564366)⟩))
        (.row ⟨110576703734, 114055813620, .zero, (.variance 309050564366)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨110576703734, 114055813620, (.direct 391506126583 388653767465), (.variance 251044497946)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 593382169971 585078944935), (.variance 225544183679)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 391506126583 388653767465), (.variance 251044497946)⟩))
        (.row ⟨110576703734, 114055813620, (.direct 391506126583 388653767465), (.variance 251044497946)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨110576703734, 114055813620, (.direct 824633666698 809644741072), (.variance 207151950215)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1950107488270), (.variance 164559115731)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3421298219255), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (5)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 809644741072), (.variance 207151950215)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3421298219255), (.variance 142034712544)⟩)))
      (.row ⟨110576703734, 114055813620, (.direct 824633666698 809644741072), (.variance 207151950215)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H3NegPart10_checked : CutTop0H3NegPart10Tree.commonOK CutTop0H3NegPart10Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
