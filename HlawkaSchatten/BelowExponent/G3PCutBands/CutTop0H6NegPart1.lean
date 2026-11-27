/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H6NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H6NegPart1Box : Box := ((((((⟨![27/68, 3/20, 0, -8], ![63/136, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop0H6NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨110576703734, 114055813620, (.direct 10180561190 4987123086), (.variance 785440410607)⟩)
      (.cut 1 (31/200)
        (.row ⟨110576703734, 112330851340, (.direct 0 1601621659), (.chord .universal 0 10180665226)⟩)
        (.row ⟨112330851339, 114055813620, (.direct 0 1691538158), (.chord .universal 0 10180665226)⟩)))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.cut 3 (1/64)
            (.cut 2 (1/16)
              (.row ⟨110576703734, 114055813620, (.direct 377054043 2793310828), (.variance 1144114699353)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 377054043 2793310828), (.chord (.secant 1165134363980 87985117935 22417501465 32016887725) 3393555298 10180665226)⟩))
            (.cut 2 (1/16)
              (.row ⟨110576703734, 114055813620, (.direct 1131165907 4086376995), (.variance 975127920043)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 1131165907 4086376995), (.chord (.secant 1348226048587 165944202795 5494640688 58943771735) 3393555298 10180665226)⟩)))
          (.cut 3 (3/64)
            (.row ⟨110576703734, 114055813620, (.direct 2150924658 5552353566), (.variance 869108679350)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 3393509060 7177786151), (.variance 794295679842)⟩)))
        (.cut 3 (3/32)
          (.row ⟨110576703734, 114055813620, (.direct 6452795533 10867308758), (.variance 737693401366)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 10180561190 15092394261), (.variance 656103316093)⟩)))
      (.cut 3 (3/16)
        (.row ⟨110576703734, 114055813620, (.direct 19358451269 24981546575), (.variance 598857804696)⟩)
        (.row ⟨110576703734, 114055813620, (.direct 30541785600 36595240909), (.variance 521593208047)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop0H6NegPart1_checked : CutTop0H6NegPart1Tree.commonOK CutTop0H6NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
