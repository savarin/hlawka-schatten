/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H3NegPart45`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H3NegPart45Box : Box := ((((((⟨![27/136, 19/100, 0, -8], ![9/34, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H3NegPart45Tree : CertTree :=
  .cut 3 (1/2)
    (.cut 3 (3/8)
      (.cut 3 (5/16)
        (.row ⟨123862991199, 126950446638, (.direct 43500437793 48045651556), (.variance 476525801262)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 58075547817 62652245712), (.variance 437235925798)⟩))
      (.cut 3 (7/16)
        (.cut 3 (13/32)
          (.row ⟨123862991199, 126950446638, (.direct 65931069018 70479533798), (.variance 407172541499)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 74148400816 78641744925), (.variance 394545525387)⟩))
        (.cut 3 (15/32)
          (.row ⟨123862991199, 126950446638, (.direct 82716570280 87129394606), (.variance 383161049754)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 91625662891 95933856336), (.variance 372823964829)⟩))))
    (.cut 3 (5/8)
      (.cut 3 (9/16)
        (.cut 3 (17/32)
          (.row ⟨123862991199, 126950446638, (.direct 100866659274 105047236997), (.variance 363379822555)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 110431305439 114462276406), (.variance 354704531822)⟩))
        (.row ⟨123862991199, 126950446638, (.direct 130501749339 134170977513), (.variance 346697063346)⟩))
      (.cut 3 (11/16)
        (.row ⟨123862991199, 126950446638, (.direct 151782739331 155011753036), (.variance 332366648244)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 174227225485 176942518418), (.variance 319873574847)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H3NegPart45_checked : CutTop4H3NegPart45Tree.commonOK CutTop4H3NegPart45Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
