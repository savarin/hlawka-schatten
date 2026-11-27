/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H0NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H0NegPart0Box : Box := (((⟨![0, 3/20, 0, -8], ![9/136, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop0H0NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3485095648656), (.variance 141349223442)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 813383153944), (.variance 206902214225)⟩))
        (.cut 3 (-5)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3485095648656), (.variance 141349223442)⟩)
          (.cut 3 (-7/2)
            (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1978600857971), (.variance 163935250153)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 824633666698 813383153944), (.variance 206902214225)⟩))))
      (.cut 3 (-5)
        (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3485095648656), (.variance 141349223442)⟩)
        (.cut 3 (-7/2)
          (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1978600857971), (.variance 163935250153)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 813383153944), (.variance 206902214225)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨110576703734, 114055813620, (.direct 30541785600 29160951079), (.variance 494629047057)⟩)
        (.cut 3 (-9/8)
          (.row ⟨110576703734, 114055813620, (.direct 331294831298 325605676223), (.variance 262954006550)⟩)
          (.cut 3 (-11/16)
            (.row ⟨110576703734, 114055813620, (.direct 151782739331 148399118307), (.variance 323029269360)⟩)
            (.cut 3 (-15/32)
              (.row ⟨110576703734, 114055813620, (.direct 82716570280 80365495629), (.variance 379307331312)⟩)
              (.cut 2 (5/16)
                (.row ⟨110576703734, 114055813620, (.direct 30541785600 29160951079), (.variance 494629047057)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨110576703734, 114055813620, (.direct 54287234842 52426561465), (.variance 424200297947)⟩)
                  (.cut 2 (13/32)
                    (.row ⟨110576703734, 114055813620, (.direct 30541785600 29160951079), (.chord (.midpoint ⟨469773433133, 121576148527, 203414458871, 340340913245, 203413944359, 238375158869⟩) 43500686443 65931360876)⟩)
                    (.row ⟨110576703734, 114055813620, (.direct 30541785600 29160951079), (.chord (.midpoint ⟨530651040444, 87482536950, 180149010508, 370971760940, 180148371021, 282711267771⟩) 65931360876 91625974997)⟩))))))))
      (.cut 3 (-9/8)
        (.row ⟨110576703734, 114055813620, (.direct 331294831298 325605676223), (.variance 262954006550)⟩)
        (.cut 3 (-11/16)
          (.row ⟨110576703734, 114055813620, (.direct 151782739331 148399118307), (.variance 323029269360)⟩)
          (.cut 3 (-15/32)
            (.row ⟨110576703734, 114055813620, (.direct 82716570280 80365495629), (.variance 379307331312)⟩)
            (.cut 3 (-23/64)
              (.row ⟨110576703734, 114055813620, (.direct 54287234842 52426561465), (.variance 424200297947)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 30541785600 29160951079), (.chord .universal 91625974997 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop0H0NegPart0_checked : CutTop0H0NegPart0Tree.commonOK CutTop0H0NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
