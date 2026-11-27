/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H5NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H5NegPart0Box : Box := (((⟨![45/136, 3/20, 0, -8], ![27/68, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop0H5NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3295013724319), (.variance 143440427051)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 757978301227), (.variance 210759896803)⟩))
        (.cut 3 (-5)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3295013724319), (.variance 143440427051)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 757978301227), (.variance 210759896803)⟩)))
      (.cut 3 (-5)
        (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3295013724319), (.variance 143440427051)⟩)
        (.row ⟨110576703734, 114055813620, (.direct 824633666698 757978301227), (.variance 210759896803)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨110576703734, 114055813620, (.direct 30541785600 22617836388), (.variance 528659432698)⟩)
        (.cut 3 (-9/8)
          (.row ⟨110576703734, 114055813620, (.direct 331294831298 297709167101), (.variance 269194334245)⟩)
          (.cut 3 (-11/16)
            (.row ⟨110576703734, 114055813620, (.direct 151782739331 131906689560), (.variance 333149978523)⟩)
            (.cut 3 (-15/32)
              (.row ⟨110576703734, 114055813620, (.direct 82716570280 68989370357), (.variance 394774634269)⟩)
              (.cut 2 (5/16)
                (.row ⟨110576703734, 114055813620, (.direct 30541785600 22617836388), (.variance 528659432698)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨110576703734, 114055813620, (.direct 54287234842 43487462066), (.chord (.midpoint ⟨294398849929, 255855750982, 239529402560, 303078513913, 267698052120, 116065308469⟩) 43500686443 91625974997)⟩)
                  (.row ⟨110576703734, 114055813620, (.direct 30541785600 22617836388), (.chord (.midpoint ⟨394207919924, 172230424057, 199696354164, 344824838987, 231316773917, 197777101988⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨110576703734, 114055813620, (.direct 331294831298 297709167101), (.variance 269194334245)⟩)
        (.cut 3 (-11/16)
          (.row ⟨110576703734, 114055813620, (.direct 151782739331 131906689560), (.variance 333149978523)⟩)
          (.cut 3 (-15/32)
            (.row ⟨110576703734, 114055813620, (.direct 82716570280 68989370357), (.variance 394774634269)⟩)
            (.cut 3 (-23/64)
              (.row ⟨110576703734, 114055813620, (.direct 54287234842 43487462066), (.chord (.midpoint ⟨445770164742, 136617254821, 178465419478, 373451407536, 212362032776, 231259356765⟩) 91625974997 274877906944)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 30541785600 22617836388), (.chord (.midpoint ⟨502002715376, 102821763239, 154211416262, 414232125432, 191216691684, 267922146188⟩) 91625974997 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop0H5NegPart0_checked : CutTop0H5NegPart0Tree.commonOK CutTop0H5NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
