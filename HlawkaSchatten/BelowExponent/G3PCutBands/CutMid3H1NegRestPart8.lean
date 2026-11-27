/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H1NegRestPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H1NegRestPart8Box : Box := ((((((((⟨![9/68, 11/100, 0, -8], ![9/34, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutMid3H1NegRestPart8Tree : RatioRemainder :=
  .cut 3 (3/16)
    (.cut 1 (3/25)
      (.cut 3 (5/32)
        (.cut 0 (27/136)
          (.cut 1 (23/200)
            (.original (.row ⟨95281442640, 97336292160, (.direct 14500097491 16031868007), (.variance 637514154570)⟩))
            (.original (.row ⟨97336292159, 99345187400, (.direct 14500097491 16104078202), (.variance 636862420963)⟩)))
          (.original (.row ⟨95281442640, 99345187400, (.direct 14500097491 16652387078), (.variance 630865552122)⟩)))
        (.cut 0 (27/136)
          (.original (.row ⟨95281442640, 99345187400, (.direct 19358451269 21070327838), (.variance 583967725187)⟩))
          (.original (.row ⟨95281442640, 99345187400, (.direct 19358451269 21652720872), (.variance 579195465836)⟩))))
      (.cut 3 (5/32)
        (.cut 0 (27/136)
          (.cut 1 (1/8)
            (.original (.row ⟨99345187399, 101311009181, (.direct 14500097491 16176794176), (.variance 636209504789)⟩))
            (.original (.row ⟨101311009180, 103236350716, (.direct 14500097491 16250020813), (.variance 635555401173)⟩)))
          (.original (.row ⟨99345187399, 103236350716, (.direct 14500097491 16849496788), (.variance 628980329744)⟩)))
        (.cut 0 (27/136)
          (.original (.row ⟨99345187399, 103236350716, (.direct 19358451269 21225473590), (.variance 583034192087)⟩))
          (.original (.row ⟨99345187399, 103236350716, (.direct 19358451269 21861761805), (.variance 577835541568)⟩)))))
    (.cut 1 (3/25)
      (.cut 0 (27/136)
        (.original (.row ⟨95281442640, 99345187400, (.direct 30541785600 32402637981), (.variance 543191764924)⟩))
        (.original (.row ⟨95281442640, 99345187400, (.direct 30541785600 33031838048), (.variance 539591700858)⟩)))
      (.cut 3 (7/32)
        (.original (.row ⟨99345187399, 103236350716, (.direct 24716051037 27339878487), (.variance 542489035665)⟩))
        (.original (.row ⟨99345187399, 103236350716, (.direct 30541785600 33257230137), (.variance 510185648729)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid3H1NegRestPart8_ok : CutMid3H1NegRestPart8Tree.ok CutMid3H1NegRestPart8Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
