/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H4NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H4NegPart0Box : Box := (((⟨![9/34, 3/20, 0, -8], ![45/136, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop0H4NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3332714901657), (.variance 143013737820)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 768943664896), (.variance 209968713381)⟩))
        (.cut 3 (-5)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3332714901657), (.variance 143013737820)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 768943664896), (.variance 209968713381)⟩)))
      (.cut 3 (-5)
        (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3332714901657), (.variance 143013737820)⟩)
        (.cut 3 (-7/2)
          (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1885919138038), (.variance 166007665932)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 768943664896), (.variance 209968713381)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨110576703734, 114055813620, (.direct 30541785600 23877116950), (.variance 521211767945)⟩)
        (.cut 3 (-9/8)
          (.row ⟨110576703734, 114055813620, (.direct 331294831298 303214533502), (.variance 267905801507)⟩)
          (.cut 3 (-11/16)
            (.row ⟨110576703734, 114055813620, (.direct 151782739331 135147648577), (.variance 331039144950)⟩)
            (.cut 3 (-15/32)
              (.row ⟨110576703734, 114055813620, (.direct 82716570280 71213150290), (.variance 391508625011)⟩)
              (.cut 2 (5/16)
                (.row ⟨110576703734, 114055813620, (.direct 30541785600 23877116950), (.variance 521211767945)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨110576703734, 114055813620, (.direct 54287234842 45225739837), (.variance 440933779640)⟩)
                  (.row ⟨110576703734, 114055813620, (.direct 30541785600 23877116950), (.chord (.midpoint ⟨420292232021, 153632688024, 195898298999, 349554979617, 221764212339, 206345790759⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨110576703734, 114055813620, (.direct 331294831298 303214533502), (.variance 267905801507)⟩)
        (.cut 3 (-11/16)
          (.row ⟨110576703734, 114055813620, (.direct 151782739331 135147648577), (.variance 331039144950)⟩)
          (.cut 3 (-15/32)
            (.row ⟨110576703734, 114055813620, (.direct 82716570280 71213150290), (.variance 391508625011)⟩)
            (.cut 2 (3/4)
              (.row ⟨110576703734, 114055813620, (.direct 30541785600 23877116950), (.chord (.midpoint ⟨495293209269, 106593290674, 164960307277, 394894776398, 193775947246, 240298198693⟩) 91625974997 174227471798)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 30541785600 23877116950), (.chord (.midpoint ⟨534473476182, 85528120192, 147843084607, 426814184264, 178652393965, 288491954989⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop0H4NegPart0_checked : CutTop0H4NegPart0Tree.commonOK CutTop0H4NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
