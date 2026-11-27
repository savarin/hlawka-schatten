/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H0NegPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H0NegPart8Box : Box := (((((⟨![0, 3/20, 0, -8], ![9/136, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop0H0NegPart8Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.cut 3 (-3/16)
        (.row ⟨110576703734, 114055813620, (.direct 19358451269 18252360866), (.chord .universal 91625974997 274877906944)⟩)
        (.row ⟨110576703734, 114055813620, (.direct 10180561190 9357729833), (.chord .universal 91625974997 274877906944)⟩))
      (.cut 3 (-1/16)
        (.row ⟨110576703734, 114055813620, (.direct 3393509060 2882648447), (.chord .universal 91625974997 274877906944)⟩)
        (.cut 3 (-1/32)
          (.row ⟨110576703734, 114055813620, (.direct 1131165907 810163794), (.chord .universal 91625974997 274877906944)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 0 77416437), (.chord (.secant 832170350059 232244198 10659318771 3393509060) 91625974997 274877906944)⟩))))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.row ⟨110576703734, 114055813620, (.direct 3393509060 3869410782), (.chord (.secant 915122534380 11608117682 3715346965 0) 91625974997 274877906944)⟩)
        (.row ⟨110576703734, 114055813620, (.direct 10180561190 10838259286), (.chord (.secant 1000948101975 32514560523 38057447 3393509060) 91625974997 274877906944)⟩))
      (.row ⟨110576703734, 114055813620, (.direct 30541785600 31381889682), (.chord (.secant 1180957534409 94145350095 3082652371 10180561190) 91625974997 274877906944)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H0NegPart8_checked : CutTop0H0NegPart8Tree.commonOK CutTop0H0NegPart8Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
