/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H6NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H6NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H6NegRestPart0Box : Box := (((⟨![27/68, 19/100, 0, -8], ![63/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop4H6NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4846594002059), (.variance 129655203197)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3184927156717), (.variance 144722469047)⟩)))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 726030418628), (.variance 213149928144)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4846594002059), (.variance 129655203197)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3184927156717), (.variance 144722469047)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1796141739130), (.variance 168141489886)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 726030418628), (.variance 213149928144)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4846594002059), (.variance 129655203197)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3184927156717), (.variance 144722469047)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1796141739130), (.variance 168141489886)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 726030418628), (.variance 213149928144)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 19058663767), (.variance 552901158756)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 281716332999), (.variance 273114816560)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 122533720987), (.variance 339642656348)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 62594252436), (.variance 404960077858)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 19058663767), (.variance 552901158756)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨123862991199, 126950446638, (.direct 54287234842 38516986043), (.chord (.midpoint ⟨285463237228, 264440932604, 237220718795, 305168361866, 270978794136, 117137129492⟩) 43500686443 91625974997)⟩))
                  (.covered)))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 281716332999), (.variance 273114816560)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 122533720987), (.variance 339642656348)⟩))
          (.cut 3 (-15/32)
            (.cut 2 (3/4)
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 62594252436), (.chord (.midpoint ⟨309963403831, 241372892493, 227324971044, 314535271507, 262002368174, 136561066428⟩) 91625974997 174227471798)⟩))
              (.covered))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop4H6NegRestPart0_ok : CutTop4H6NegRestPart0Tree.geometryOK CutTop4H6NegPowerCache CutTop4H6NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
