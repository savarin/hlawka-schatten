/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2NegPart25`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H2NegPart25Box : Box := ((⟨![9/34, 11/100, 0, -8], ![27/68, 13/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid3H2NegPart25Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨95281442640, 103236350716, .zero, (.variance 309079947965)⟩))
        (.row ⟨95281442640, 103236350716, .zero, (.variance 309079947965)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨95281442640, 103236350716, (.direct 391506126583 388086418216), (.variance 251140548647)⟩)
            (.row ⟨95281442640, 103236350716, (.direct 593382169971 583429842323), (.variance 225710946833)⟩))
          (.row ⟨95281442640, 103236350716, (.direct 391506126583 388086418216), (.variance 251140548647)⟩))
        (.row ⟨95281442640, 103236350716, (.direct 391506126583 388086418216), (.variance 251140548647)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨95281442640, 103236350716, (.direct 824633666698 806670557967), (.variance 207351675197)⟩)
            (.row ⟨95281442640, 103236350716, (.direct 2002014560937 1939825487763), (.variance 164787071751)⟩))
          (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3401056459895), (.variance 142255583784)⟩))
        (.cut 3 (5)
          (.row ⟨95281442640, 103236350716, (.direct 824633666698 806670557967), (.variance 207351675197)⟩)
          (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3401056459895), (.variance 142255583784)⟩)))
      (.row ⟨95281442640, 103236350716, (.direct 824633666698 806670557967), (.variance 207351675197)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H2NegPart25_checked : CutMid3H2NegPart25Tree.commonOK CutMid3H2NegPart25Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
