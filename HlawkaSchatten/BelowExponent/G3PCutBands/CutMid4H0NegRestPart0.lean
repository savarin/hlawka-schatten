/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H0NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H0NegRestPart0Box : Box := (((⟨![0, 13/100, 0, -8], ![9/68, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid4H0NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3451935654778), (.variance 141703525135)⟩))
          (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 803696647832), (.variance 207552313098)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨103236350715, 110576703735, (.direct 5340438828596 5236058292318), (.variance 127057417223)⟩))
            (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3451935654778), (.variance 141703525135)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1958422689430), (.variance 164375870807)⟩))
            (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 803696647832), (.variance 207552313098)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨103236350715, 110576703735, (.direct 5340438828596 5236058292318), (.variance 127057417223)⟩))
          (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3451935654778), (.variance 141703525135)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1958422689430), (.variance 164375870807)⟩))
          (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 803696647832), (.variance 207552313098)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 27985660781), (.variance 499986215444)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨103236350715, 110576703735, (.direct 331294831298 320714552761), (.variance 263998250217)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨103236350715, 110576703735, (.direct 151782739331 145495270497), (.variance 324705219965)⟩))
            (.cut 2 (5/16)
              (.cut 3 (-15/32)
                (.original (.row ⟨103236350715, 110576703735, (.direct 82716570280 78352119413), (.variance 381835792571)⟩))
                (.cut 0 (9/136)
                  (.cut 1 (7/50)
                    (.original (.row ⟨103236350715, 106974752992, (.direct 30541785600 29345201151), (.variance 493813915793)⟩))
                    (.original (.row ⟨106974752991, 110576703735, (.direct 30541785600 29253520552), (.variance 494218705430)⟩)))
                  (.cut 1 (7/50)
                    (.original (.row ⟨103236350715, 106974752992, (.direct 30541785600 28166157943), (.variance 499145209562)⟩))
                    (.original (.row ⟨106974752991, 110576703735, (.direct 30541785600 27985660781), (.variance 499986215444)⟩)))))
              (.cut 3 (-15/32)
                (.original (.row ⟨103236350715, 110576703735, (.direct 82716570280 78352119413), (.variance 381835792571)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨103236350715, 110576703735, (.direct 54287234842 50836494327), (.variance 427635297765)⟩))
                  (.cut 2 (13/32)
                    (.cut 0 (9/136)
                      (.cut 1 (7/50)
                        (.original (.row ⟨103236350715, 106974752992, (.direct 30541785600 29345201151), (.chord (.midpoint ⟨468510457494, 122344315644, 203887864313, 339780043397, 203887352585, 238375158869⟩) 43500686443 65931360876)⟩))
                        (.original (.row ⟨106974752991, 110576703735, (.direct 30541785600 29253520552), (.chord (.midpoint ⟨469138375012, 121962085009, 203652538662, 340058568234, 203652025550, 238375158869⟩) 43500686443 65931360876)⟩)))
                      (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 27985660781), (.chord (.midpoint ⟨443055151531, 138378143276, 206931659290, 336226361424, 213368170196, 230059298802⟩) 43500686443 65931360876)⟩)))
                    (.covered))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨103236350715, 110576703735, (.direct 331294831298 320714552761), (.variance 263998250217)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨103236350715, 110576703735, (.direct 151782739331 145495270497), (.variance 324705219965)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨103236350715, 110576703735, (.direct 82716570280 78352119413), (.variance 381835792571)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutMid4H0NegRestPart0_ok : CutMid4H0NegRestPart0Tree.geometryOK CutMid4H0NegPowerCache CutMid4H0NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
