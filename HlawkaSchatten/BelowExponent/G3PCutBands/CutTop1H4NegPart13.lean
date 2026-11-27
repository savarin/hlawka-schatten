/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H4NegPart13`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H4NegPart13Box : Box := ((⟨![9/34, 4/25, 0, -8], ![45/136, 17/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop1H4NegPart13Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨114055813619, 117423580140, .zero, (.variance 308756710527)⟩))
        (.row ⟨114055813619, 117423580140, .zero, (.variance 308756710527)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨114055813619, 117423580140, (.direct 391506126583 387698717333), (.variance 251206287334)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 593382169971 582303397205), (.variance 225825199274)⟩))
          (.row ⟨114055813619, 117423580140, (.direct 391506126583 387698717333), (.variance 251206287334)⟩))
        (.row ⟨114055813619, 117423580140, (.direct 391506126583 387698717333), (.variance 251206287334)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨114055813619, 117423580140, (.direct 824633666698 804639538241), (.variance 207488598738)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1932807593579), (.variance 164943538535)⟩))
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3387243402077), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (5)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 804639538241), (.variance 207488598738)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3387243402077), (.variance 142407261625)⟩)))
      (.row ⟨114055813619, 117423580140, (.direct 824633666698 804639538241), (.variance 207488598738)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H4NegPart13_checked : CutTop1H4NegPart13Tree.commonOK CutTop1H4NegPart13Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
