/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H6NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H6NegPart0Box : Box := (((⟨![27/68, 3/20, 0, -8], ![63/136, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop0H6NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3257471086893), (.variance 143871488120)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 747071174114), (.variance 211561337848)⟩))
        (.cut 3 (-5)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3257471086893), (.variance 143871488120)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 747071174114), (.variance 211561337848)⟩)))
      (.cut 3 (-5)
        (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3257471086893), (.variance 143871488120)⟩)
        (.row ⟨110576703734, 114055813620, (.direct 824633666698 747071174114), (.variance 211561337848)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨110576703734, 114055813620, (.direct 30541785600 21383917631), (.variance 536482890766)⟩)
        (.cut 3 (-9/8)
          (.row ⟨110576703734, 114055813620, (.direct 331294831298 292241121428), (.variance 270504244543)⟩)
          (.cut 3 (-11/16)
            (.row ⟨110576703734, 114055813620, (.direct 151782739331 128694857214), (.variance 335307417723)⟩)
            (.cut 3 (-15/32)
              (.row ⟨110576703734, 114055813620, (.direct 82716570280 66791736837), (.variance 398135441932)⟩)
              (.cut 2 (5/16)
                (.row ⟨110576703734, 114055813620, (.direct 30541785600 21383917631), (.variance 536482890766)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨110576703734, 114055813620, (.direct 54287234842 41774458702), (.chord (.midpoint ⟨272140863351, 277625046209, 242607890390, 300344811592, 275888614910, 103430588995⟩) 43500686443 91625974997)⟩)
                  (.row ⟨110576703734, 114055813620, (.direct 30541785600 21383917631), (.chord (.midpoint ⟨368745652643, 191600939960, 203443832731, 340306047477, 240597246164, 188936457615⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨110576703734, 114055813620, (.direct 331294831298 292241121428), (.variance 270504244543)⟩)
        (.cut 3 (-11/16)
          (.row ⟨110576703734, 114055813620, (.direct 151782739331 128694857214), (.variance 335307417723)⟩)
          (.cut 3 (-15/32)
            (.row ⟨110576703734, 114055813620, (.direct 82716570280 66791736837), (.variance 398135441932)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 30541785600 21383917631), (.chord (.midpoint ⟨470289298241, 121263121749, 160398354129, 402831033090, 203220490132, 221962549319⟩) 91625974997 274877906944)⟩)))))

set_option maxRecDepth 16000 in
theorem CutTop0H6NegPart0_checked : CutTop0H6NegPart0Tree.commonOK CutTop0H6NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
