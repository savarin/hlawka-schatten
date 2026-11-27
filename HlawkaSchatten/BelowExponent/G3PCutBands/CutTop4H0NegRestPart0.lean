/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H0NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H0NegRestPart0Box : Box := (((⟨![0, 19/100, 0, -8], ![9/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop4H0NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3474432550540), (.variance 141462688883)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 810267368430), (.variance 207110256167)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 5268852180703), (.variance 126849859450)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3474432550540), (.variance 141462688883)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1972111702202), (.variance 164076329775)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 810267368430), (.variance 207110256167)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 5268852180703), (.variance 126849859450)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3474432550540), (.variance 141462688883)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1972111702202), (.variance 164076329775)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 810267368430), (.variance 207110256167)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 28781526774), (.variance 496328297135)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 324031764727), (.variance 263287861202)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 147464150805), (.variance 323564334536)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 79716783952), (.variance 380113194787)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 28781526774), (.variance 496328297135)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨123862991199, 126950446638, (.direct 54287234842 51913893508), (.chord (.midpoint ⟨417246798278, 155741395957, 222883179591, 318969943301, 222882786980, 168647478831⟩) 43500686443 91625974997)⟩))
                  (.cut 2 (13/32)
                    (.cut 0 (9/272)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 29656938877), (.chord (.midpoint ⟨466383083264, 123643998598, 204684579606, 338841139272, 204684072585, 244210969874⟩) 43500686443 65931360876)⟩))
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 28781526774), (.chord (.midpoint ⟨454904500039, 130782640447, 205719734801, 337630532494, 208968556990, 241052397967⟩) 43500686443 65931360876)⟩)))
                    (.covered))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 324031764727), (.variance 263287861202)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 147464150805), (.variance 323564334536)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 79716783952), (.variance 380113194787)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop4H0NegRestPart0_ok : CutTop4H0NegRestPart0Tree.geometryOK CutTop4H0NegPowerCache CutTop4H0NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
