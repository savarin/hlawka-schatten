/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H3NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H3NegRestPart0Box : Box := (((⟨![27/136, 19/100, 0, -8], ![9/34, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop4H3NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3328518067527), (.variance 143060934194)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 767722422097), (.variance 210056123064)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 5056096039929), (.variance 128226382466)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3328518067527), (.variance 143060934194)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1883368121802), (.variance 166066516566)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 767722422097), (.variance 210056123064)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 5056096039929), (.variance 128226382466)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3328518067527), (.variance 143060934194)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1883368121802), (.variance 166066516566)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 767722422097), (.variance 210056123064)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 23735955714), (.variance 522021684743)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 302600988705), (.variance 268047934632)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 134786109438), (.variance 331271433885)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 70964779229), (.variance 391866975276)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 23735955714), (.variance 522021684743)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨123862991199, 126950446638, (.direct 54287234842 45031357847), (.chord (.midpoint ⟨349055415013, 207454176976, 230131190736, 311809135144, 247760861197, 144534104837⟩) 43500686443 91625974997)⟩))
                  (.cut 0 (63/272)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 24551840115), (.chord (.midpoint ⟨450534885409, 133556585781, 190634759989, 356375633793, 210593572943, 224794639817⟩) 43500686443 91625974997)⟩))
                    (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 23735955714), (.chord (.midpoint ⟨438104928173, 141620497231, 192163256484, 354362072973, 215199861715, 221442477340⟩) 43500686443 91625974997)⟩)))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 302600988705), (.variance 268047934632)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 134786109438), (.variance 331271433885)⟩))
          (.cut 3 (-15/32)
            (.cut 2 (3/4)
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 70964779229), (.chord (.midpoint ⟨383627436274, 180129376495, 216836839525, 325255259288, 235176913951, 167920022591⟩) 91625974997 174227471798)⟩))
              (.covered))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop4H3NegRestPart0_ok : CutTop4H3NegRestPart0Tree.geometryOK CutTop4H3NegPowerCache CutTop4H3NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
