/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H3NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H3NegPart0Box : Box := (((⟨![27/136, 3/20, 0, -8], ![9/34, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop0H3NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3370574147296), (.variance 142591345294)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 779967046500), (.variance 209187565521)⟩))
        (.cut 3 (-5)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3370574147296), (.variance 142591345294)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 779967046500), (.variance 209187565521)⟩)))
      (.cut 3 (-5)
        (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3370574147296), (.variance 142591345294)⟩)
        (.cut 3 (-7/2)
          (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1908935568346), (.variance 165481189796)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 779967046500), (.variance 209187565521)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨110576703734, 114055813620, (.direct 30541785600 25161401927), (.variance 514110098967)⟩)
        (.cut 3 (-9/8)
          (.row ⟨110576703734, 114055813620, (.direct 331294831298 308757041984), (.variance 266638057683)⟩)
          (.cut 3 (-11/16)
            (.row ⟨110576703734, 114055813620, (.direct 151782739331 138417549710), (.variance 328973224542)⟩)
            (.cut 3 (-15/32)
              (.row ⟨110576703734, 114055813620, (.direct 82716570280 73462860305), (.variance 388332939596)⟩)
              (.cut 2 (5/16)
                (.row ⟨110576703734, 114055813620, (.direct 30541785600 25161401927), (.variance 514110098967)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨110576703734, 114055813620, (.direct 54287234842 46989033907), (.variance 436539618478)⟩)
                  (.row ⟨110576703734, 114055813620, (.direct 30541785600 25161401927), (.chord (.midpoint ⟨446988235641, 135831233634, 192047261420, 354513917805, 211910273719, 214669095485⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨110576703734, 114055813620, (.direct 331294831298 308757041984), (.variance 266638057683)⟩)
        (.cut 3 (-11/16)
          (.row ⟨110576703734, 114055813620, (.direct 151782739331 138417549710), (.variance 328973224542)⟩)
          (.cut 3 (-15/32)
            (.row ⟨110576703734, 114055813620, (.direct 82716570280 73462860305), (.variance 388332939596)⟩)
            (.cut 2 (3/4)
              (.row ⟨110576703734, 114055813620, (.direct 30541785600 25161401927), (.chord (.midpoint ⟨526278095734, 89744823510, 159467331345, 404498293644, 181853902790, 249101962314⟩) 91625974997 174227471798)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 30541785600 25161401927), (.chord (.midpoint ⟨567689247897, 69439079732, 141273833857, 440802545938, 165426840368, 297051470956⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop0H3NegPart0_checked : CutTop0H3NegPart0Tree.commonOK CutTop0H3NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
