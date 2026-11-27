/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid1H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H0NegPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H0NegPart5Box : Box := ((⟨![0, 7/100, 0, -8], ![9/68, 9/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid1H0NegPart5Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨76698504228, 86531900009, .zero, (.variance 309737727641)⟩))
        (.row ⟨76698504228, 86531900009, .zero, (.variance 309737727641)⟩))
      (.row ⟨76698504228, 86531900009, (.direct 391506126583 390732854131), (.variance 250694020535)⟩))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.row ⟨76698504228, 86531900009, (.direct 824633666698 820564556467), (.variance 206426516256)⟩)
          (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3495759616946), (.variance 141236186021)⟩))
        (.row ⟨76698504228, 86531900009, (.direct 824633666698 820564556467), (.variance 206426516256)⟩))
      (.row ⟨76698504228, 86531900009, (.direct 824633666698 820564556467), (.variance 206426516256)⟩))

set_option maxRecDepth 16000 in
theorem CutMid1H0NegPart5_checked : CutMid1H0NegPart5Tree.geometryOK CutMid1H0NegPowerCache CutMid1H0NegPart5Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
