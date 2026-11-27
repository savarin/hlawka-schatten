/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H2NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H2NegPart0Box : Box := (((⟨![9/34, 1/20, 0, -8], ![27/68, 7/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid0H2NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3427559477974), (.variance 141966725503)⟩)
          (.row ⟨65259754744, 76698504229, (.direct 824633666698 796581574354), (.variance 208036164541)⟩))
        (.cut 3 (-5)
          (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3427559477974), (.variance 141966725503)⟩)
          (.row ⟨65259754744, 76698504229, (.direct 824633666698 796581574354), (.variance 208036164541)⟩)))
      (.row ⟨65259754744, 76698504229, (.direct 824633666698 796581574354), (.variance 208036164541)⟩))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-9/8)
          (.row ⟨65259754744, 76698504229, (.direct 331294831298 317125512582), (.variance 264777369942)⟩)
          (.row ⟨65259754744, 76698504229, (.direct 30541785600 27130517377), (.variance 504065810014)⟩))
        (.cut 3 (-9/8)
          (.row ⟨65259754744, 76698504229, (.direct 331294831298 317125512582), (.variance 264777369942)⟩)
          (.row ⟨65259754744, 76698504229, (.direct 30541785600 27130517377), (.variance 504065810014)⟩)))
      (.row ⟨65259754744, 76698504229, (.direct 30541785600 27130517377), (.variance 504065810014)⟩))

set_option maxRecDepth 16000 in
theorem CutMid0H2NegPart0_checked : CutMid0H2NegPart0Tree.commonOK CutMid0H2NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
