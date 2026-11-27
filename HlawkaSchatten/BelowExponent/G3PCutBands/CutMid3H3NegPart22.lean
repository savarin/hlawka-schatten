/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3NegPart22`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3NegPart22Box : Box := ((((⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid3H3NegPart22Tree : CertTree :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.cut 3 (5/16)
            (.row ⟨95281442640, 103236350716, (.direct 43500437793 49214007739), (.variance 475264391674)⟩)
            (.row ⟨95281442640, 103236350716, (.direct 58075547817 63822512749), (.variance 436372639222)⟩))
          (.row ⟨95281442640, 103236350716, (.direct 91625662891 97028037856), (.variance 406556477009)⟩))
        (.cut 3 (5/8)
          (.row ⟨95281442640, 103236350716, (.direct 130501749339 135099007243), (.variance 363045111981)⟩)
          (.row ⟨95281442640, 103236350716, (.direct 174227225485 177627343942), (.variance 332181334489)⟩)))
      (.cut 0 (63/136)
        (.cut 3 (1/2)
          (.cut 3 (3/8)
            (.cut 0 (117/272)
              (.cut 3 (5/16)
                (.row ⟨95281442640, 103236350716, (.direct 43500437793 48123012997), (.variance 475264391674)⟩)
                (.row ⟨95281442640, 103236350716, (.direct 58075547817 62729807787), (.variance 436372639222)⟩))
              (.row ⟨95281442640, 103236350716, (.direct 58075547817 63093268760), (.variance 474202741226)⟩))
            (.row ⟨95281442640, 103236350716, (.direct 91625662891 96346546193), (.variance 406556477009)⟩))
          (.row ⟨95281442640, 103236350716, (.direct 174227225485 177201034594), (.variance 363045111981)⟩))
        (.cut 3 (1/2)
          (.cut 3 (3/8)
            (.cut 3 (5/16)
              (.row ⟨95281442640, 103236350716, (.direct 43500437793 49214007739), (.variance 473149133032)⟩)
              (.row ⟨95281442640, 103236350716, (.direct 58075547817 63822512749), (.variance 434920538701)⟩))
            (.row ⟨95281442640, 103236350716, (.direct 91625662891 97028037856), (.variance 405518029401)⟩))
          (.row ⟨95281442640, 103236350716, (.direct 174227225485 177627343942), (.variance 362479386518)⟩))))
    (.cut 0 (63/136)
      (.row ⟨95281442640, 103236350716, (.direct 174227225485 177201034594), (.variance 475264391674)⟩)
      (.row ⟨95281442640, 103236350716, (.direct 174227225485 177627343942), (.variance 473149133032)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H3NegPart22_checked : CutMid3H3NegPart22Tree.commonOK CutMid3H3NegPart22Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
