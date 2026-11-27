/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0NegPart16`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0NegPart16Box : Box := ((⟨![0, 9/100, 0, -8], ![9/68, 11/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid2H0NegPart16Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨86531900008, 95281442641, .zero, (.variance 309737727641)⟩))
        (.row ⟨86531900008, 95281442641, .zero, (.variance 309737727641)⟩))
      (.row ⟨86531900008, 95281442641, (.direct 391506126583 390550995724), (.variance 250724582901)⟩))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.row ⟨86531900008, 95281442641, (.direct 824633666698 819608101796), (.variance 206489568225)⟩)
          (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3489228722517), (.variance 141305361376)⟩))
        (.row ⟨86531900008, 95281442641, (.direct 824633666698 819608101796), (.variance 206489568225)⟩))
      (.row ⟨86531900008, 95281442641, (.direct 824633666698 819608101796), (.variance 206489568225)⟩))

set_option maxRecDepth 16000 in
theorem CutMid2H0NegPart16_checked : CutMid2H0NegPart16Tree.commonOK CutMid2H0NegPart16Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
