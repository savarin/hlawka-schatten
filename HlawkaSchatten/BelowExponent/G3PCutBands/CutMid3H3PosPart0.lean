/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3PosPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3PosPart0Box : Box := (((⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid3H3PosPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3280138297655), (.variance 143610480416)⟩)
          (.row ⟨95281442640, 103236350716, (.direct 824633666698 753655136693), (.variance 211075805581)⟩))
        (.cut 3 (-5)
          (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3280138297655), (.variance 143610480416)⟩)
          (.row ⟨95281442640, 103236350716, (.direct 824633666698 753655136693), (.variance 211075805581)⟩)))
      (.row ⟨95281442640, 103236350716, (.direct 824633666698 753655136693), (.variance 211075805581)⟩))
    (.cut 2 (1/2)
      (.row ⟨95281442640, 103236350716, (.direct 30541785600 22126494882), (.variance 531708638969)⟩)
      (.row ⟨95281442640, 103236350716, (.direct 30541785600 22126494882), (.chord .universal 91625974997 274877906944)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H3PosPart0_checked : CutMid3H3PosPart0Tree.commonOK CutMid3H3PosPart0Box true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
