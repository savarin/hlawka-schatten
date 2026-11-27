/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1NegPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1NegPart8Box : Box := ((((((((⟨![9/68, 9/100, 0, -8], ![9/34, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutMid2H1NegPart8Tree : CertTree :=
  .cut 3 (3/16)
    (.cut 1 (1/10)
      (.cut 0 (27/136)
        (.cut 3 (5/32)
          (.row ⟨86531900008, 91020629598, (.direct 14500097491 15818224144), (.variance 640109359728)⟩)
          (.row ⟨86531900008, 91020629598, (.direct 19358451269 20766164879), (.variance 585820459603)⟩))
        (.cut 3 (5/32)
          (.row ⟨86531900008, 91020629598, (.direct 14500097491 16266899494), (.variance 634633800254)⟩)
          (.row ⟨86531900008, 91020629598, (.direct 19358451269 21243410433), (.variance 581904804028)⟩)))
      (.cut 0 (27/136)
        (.cut 3 (5/32)
          (.cut 1 (21/200)
            (.row ⟨91020629597, 93177423805, (.direct 14500097491 15888945715), (.variance 638814093430)⟩)
            (.row ⟨93177423804, 95281442641, (.direct 14500097491 15960158766), (.variance 638164710456)⟩))
          (.row ⟨91020629597, 95281442641, (.direct 19358451269 20917237661), (.variance 584896466897)⟩))
        (.cut 3 (5/32)
          (.row ⟨91020629597, 95281442641, (.direct 14500097491 16458206969), (.variance 632750028726)⟩)
          (.row ⟨91020629597, 95281442641, (.direct 19358451269 21446622461), (.variance 580551876201)⟩))))
    (.cut 1 (1/10)
      (.row ⟨86531900008, 91020629598, (.direct 30541785600 32589826626), (.variance 544584267441)⟩)
      (.row ⟨91020629597, 95281442641, (.direct 30541785600 32809388292), (.variance 543890161284)⟩))

set_option maxRecDepth 16000 in
theorem CutMid2H1NegPart8_checked : CutMid2H1NegPart8Tree.commonOK CutMid2H1NegPart8Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
