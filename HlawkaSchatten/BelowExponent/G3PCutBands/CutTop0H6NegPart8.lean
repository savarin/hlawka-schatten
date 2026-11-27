/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H6NegPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H6NegPart8Box : Box := ((⟨![27/68, 3/20, 0, -8], ![63/136, 4/25, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop0H6NegPart8Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨110576703734, 114055813620, .zero, (.variance 308368571105)⟩))
        (.row ⟨110576703734, 114055813620, .zero, (.variance 308368571105)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨110576703734, 114055813620, (.direct 391506126583 386519233386), (.variance 251406792182)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 593382169971 578878857361), (.variance 226174261541)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 391506126583 386519233386), (.variance 251406792182)⟩))
        (.row ⟨110576703734, 114055813620, (.direct 391506126583 386519233386), (.variance 251406792182)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.row ⟨110576703734, 114055813620, (.direct 824633666698 798467692891), (.variance 207907371786)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 1366046989981 1310970832784), (.variance 182592535552)⟩))
            (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1911499306169), (.variance 165423043082)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3345317110211), (.variance 142872466558)⟩))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨110576703734, 114055813620, (.direct 824633666698 798467692891), (.variance 207907371786)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1911499306169), (.variance 165423043082)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3345317110211), (.variance 142872466558)⟩)))
      (.row ⟨110576703734, 114055813620, (.direct 824633666698 798467692891), (.variance 207907371786)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H6NegPart8_checked : CutTop0H6NegPart8Tree.commonOK CutTop0H6NegPart8Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
