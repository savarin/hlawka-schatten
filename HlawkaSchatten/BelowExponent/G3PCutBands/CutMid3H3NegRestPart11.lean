/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H3NegRestPart11`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H3NegRestPart11Box : Box := ((⟨![27/68, 11/100, 0, -8], ![9/17, 13/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid3H3NegRestPart11Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨95281442640, 103236350716, .zero, (.variance 308752838673)⟩)))
        (.original (.row ⟨95281442640, 103236350716, .zero, (.variance 308752838673)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.cut 3 (23/16)
              (.original (.row ⟨95281442640, 103236350716, (.direct 391506126583 386948835111), (.variance 251333673309)⟩))
              (.original (.row ⟨95281442640, 103236350716, (.direct 488587506629 479942649338), (.variance 237551511866)⟩)))
            (.original (.row ⟨95281442640, 103236350716, (.direct 593382169971 580125755146), (.variance 226046864695)⟩)))
          (.original (.row ⟨95281442640, 103236350716, (.direct 391506126583 386948835111), (.variance 251333673309)⟩)))
        (.original (.row ⟨95281442640, 103236350716, (.direct 391506126583 386948835111), (.variance 251333673309)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.cut 3 (11/4)
              (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 800714427652), (.variance 207754454610)⟩))
              (.original (.row ⟨95281442640, 103236350716, (.direct 1366046989981 1315692846822), (.variance 182420707588)⟩)))
            (.original (.row ⟨95281442640, 103236350716, (.direct 2002014560937 1919253070644), (.variance 165247781415)⟩)))
          (.original (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3360571001505), (.variance 142702365523)⟩)))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 800714427652), (.variance 207754454610)⟩))
            (.original (.row ⟨95281442640, 103236350716, (.direct 2002014560937 1919253070644), (.variance 165247781415)⟩)))
          (.original (.row ⟨95281442640, 103236350716, (.direct 3523554676644 3360571001505), (.variance 142702365523)⟩))))
      (.original (.row ⟨95281442640, 103236350716, (.direct 824633666698 800714427652), (.variance 207754454610)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid3H3NegRestPart11_ok : CutMid3H3NegRestPart11Tree.geometryOK CutMid3H3NegPowerCache CutMid3H3NegRestPart11Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
