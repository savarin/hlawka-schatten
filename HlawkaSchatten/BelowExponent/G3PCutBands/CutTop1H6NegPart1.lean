/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H6NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H6NegPart1Box : Box := ((((((⟨![27/68, 4/25, 0, -8], ![63/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop1H6NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 4683575983), (.variance 798463028449)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 0 1878293089), (.chord .universal 0 10180665226)⟩))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.cut 3 (1/64)
            (.cut 2 (1/16)
              (.row ⟨114055813619, 117423580140, (.direct 377054043 3013327910), (.variance 1111372463679)⟩)
              (.row ⟨114055813619, 117423580140, (.direct 377054043 3013327910), (.chord (.secant 1197471457660 100703473219 19280196939 35771288761) 3393555298 10180665226)⟩))
            (.row ⟨114055813619, 117423580140, (.direct 1131165907 4334754943), (.variance 956134582069)⟩))
          (.row ⟨114055813619, 117423580140, (.direct 3393509060 7472665123), (.variance 856377286143)⟩))
        (.row ⟨114055813619, 117423580140, (.direct 10180561190 15453355456), (.variance 730586825090)⟩))
      (.cut 3 (3/16)
        (.row ⟨114055813619, 117423580140, (.direct 19358451269 25384668494), (.variance 595576315105)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 37023311985), (.variance 519684653512)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop1H6NegPart1_checked : CutTop1H6NegPart1Tree.commonOK CutTop1H6NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
