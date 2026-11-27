/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H2NegRestPart15`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H2NegRestPart15Box : Box := ((((((((⟨![9/34, 9/100, 0, -8], ![27/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutMid2H2NegRestPart15Tree : RatioRemainder :=
  .cut 3 (3/16)
    (.cut 1 (1/10)
      (.cut 0 (45/136)
        (.original (.row ⟨86531900008, 91020629598, (.direct 19358451269 21724646269), (.variance 629314711110)⟩))
        (.original (.row ⟨86531900008, 91020629598, (.direct 19358451269 22209849048), (.variance 624144612035)⟩)))
      (.cut 0 (45/136)
        (.original (.row ⟨91020629597, 95281442641, (.direct 19358451269 21980874591), (.variance 626877841079)⟩))
        (.original (.row ⟨91020629597, 95281442641, (.direct 19358451269 22519962788), (.variance 621187395016)⟩))))
    (.cut 1 (1/10)
      (.original (.row ⟨86531900008, 91020629598, (.direct 30541785600 33632031987), (.variance 538745175274)⟩))
      (.original (.row ⟨91020629597, 95281442641, (.direct 30541785600 33965417195), (.variance 537409808706)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid2H2NegRestPart15_ok : CutMid2H2NegRestPart15Tree.geometryOK CutMid2H2NegPowerCache CutMid2H2NegRestPart15Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
