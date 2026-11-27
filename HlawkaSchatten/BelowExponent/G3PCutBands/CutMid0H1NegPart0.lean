/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H1NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H1NegPart0Box : Box := (((⟨![9/68, 1/20, 0, -8], ![9/34, 7/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid0H1NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3459458327159), (.variance 141622772719)⟩)
          (.row ⟨65259754744, 76698504229, (.direct 824633666698 805893367648), (.variance 207404018945)⟩))
        (.cut 3 (-5)
          (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3459458327159), (.variance 141622772719)⟩)
          (.row ⟨65259754744, 76698504229, (.direct 824633666698 805893367648), (.variance 207404018945)⟩)))
      (.row ⟨65259754744, 76698504229, (.direct 824633666698 805893367648), (.variance 207404018945)⟩))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-9/8)
          (.row ⟨65259754744, 76698504229, (.direct 331294831298 321823268494), (.variance 263759788451)⟩)
          (.row ⟨65259754744, 76698504229, (.direct 30541785600 28251083232), (.variance 498751859057)⟩))
        (.cut 3 (-9/8)
          (.row ⟨65259754744, 76698504229, (.direct 331294831298 321823268494), (.variance 263759788451)⟩)
          (.row ⟨65259754744, 76698504229, (.direct 30541785600 28251083232), (.variance 498751859057)⟩)))
      (.row ⟨65259754744, 76698504229, (.direct 30541785600 28251083232), (.chord .universal 91625974997 274877906944)⟩))

set_option maxRecDepth 16000 in
theorem CutMid0H1NegPart0_checked : CutMid0H1NegPart0Tree.commonOK CutMid0H1NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
