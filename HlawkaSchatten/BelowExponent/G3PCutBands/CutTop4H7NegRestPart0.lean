/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H7NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7NegRestPart0Box : Box := (((⟨![63/136, 19/100, 0, -8], ![9/17, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop4H7NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4777489351785), (.variance 130143691457)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3137584503365), (.variance 145291126658)⟩)))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 712324780632), (.variance 214216297194)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4777489351785), (.variance 130143691457)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3137584503365), (.variance 145291126658)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1767406687117), (.variance 168853068621)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 712324780632), (.variance 214216297194)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4777489351785), (.variance 130143691457)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3137584503365), (.variance 145291126658)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1767406687117), (.variance 168853068621)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 712324780632), (.variance 214216297194)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 17585057964), (.variance 564675750160)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 274877906944), (.variance 274877906944)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 118546014691), (.variance 342597982457)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 59891013431), (.variance 409668707255)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 17585057964), (.variance 564675750160)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨123862991199, 126950446638, (.direct 54287234842 36429942350), (.chord (.midpoint ⟨265329708920, 284550116420, 239550656231, 303059434860, 278408747001, 106945794918⟩) 43500686443 91625974997)⟩))
                  (.covered)))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 274877906944), (.variance 274877906944)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 118546014691), (.variance 342597982457)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 59891013431), (.chord (.midpoint ⟨345127508776, 210711928954, 206639873058, 336563146537, 249189759458, 124919151789⟩) 91625974997 274877906944)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop4H7NegRestPart0_ok : CutTop4H7NegRestPart0Tree.geometryOK CutTop4H7NegPowerCache CutTop4H7NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
