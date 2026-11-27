/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H7NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H7NegPart1Box : Box := ((((((⟨![63/136, 3/20, 0, -8], ![9/17, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop0H7NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨110576703734, 114055813620, (.direct 10180561190 4360376299), (.variance 813554205410)⟩)
      (.cut 1 (31/200)
        (.row ⟨110576703734, 112330851340, (.direct 0 1979133040), (.chord .universal 0 10180665226)⟩)
        (.row ⟨112330851339, 114055813620, (.direct 0 2090243372), (.chord .universal 0 10180665226)⟩)))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.cut 3 (1/64)
            (.cut 2 (1/16)
              (.row ⟨110576703734, 114055813620, (.direct 377054043 3260414368), (.variance 1073208567141)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 377054043 3260414368), (.chord (.secant 1183343766918 95084956512 26564838695 40877806807) 3393555298 10180665226)⟩))
            (.row ⟨110576703734, 114055813620, (.direct 1131165907 4611965113), (.variance 933225392363)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 3393509060 7799477524), (.variance 840737264642)⟩))
        (.row ⟨110576703734, 114055813620, (.direct 10180561190 15850900736), (.variance 721687469883)⟩))
      (.cut 3 (3/16)
        (.row ⟨110576703734, 114055813620, (.direct 19358451269 25827359501), (.variance 591400553537)⟩)
        (.row ⟨110576703734, 114055813620, (.direct 30541785600 37492614599), (.variance 517238743274)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop0H7NegPart1_checked : CutTop0H7NegPart1Tree.commonOK CutTop0H7NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
