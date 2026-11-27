/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid4H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H1NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H1NegRestPart0Box : Box := (((⟨![9/68, 13/100, 0, -8], ![9/34, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid4H1NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3380833448800), (.variance 142477913149)⟩))
          (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 782956269972), (.variance 208978139037)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨103236350715, 110576703735, (.direct 5340438828596 5132391736386), (.variance 127724483317)⟩))
            (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3380833448800), (.variance 142477913149)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1915173899259), (.variance 165339873064)⟩))
            (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 782956269972), (.variance 208978139037)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨103236350715, 110576703735, (.direct 5340438828596 5132391736386), (.variance 127724483317)⟩))
          (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3380833448800), (.variance 142477913149)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1915173899259), (.variance 165339873064)⟩))
          (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 782956269972), (.variance 208978139037)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 25512753545), (.variance 512246601900)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨103236350715, 110576703735, (.direct 331294831298 310261370091), (.variance 266298918761)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨103236350715, 110576703735, (.direct 151782739331 139306251367), (.variance 328422366710)⟩))
            (.cut 0 (27/136)
              (.cut 3 (-15/32)
                (.original (.row ⟨103236350715, 110576703735, (.direct 82716570280 76202642520), (.variance 384627283248)⟩))
                (.cut 0 (45/272)
                  (.cut 1 (7/50)
                    (.cut 3 (-23/64)
                      (.original (.row ⟨103236350715, 106974752992, (.direct 54287234842 50290785351), (.variance 428845569349)⟩))
                      (.cut 2 (5/16)
                        (.original (.row ⟨103236350715, 106974752992, (.direct 30541785600 27583351945), (.variance 501885607386)⟩))
                        (.original (.row ⟨103236350715, 106974752992, (.direct 30541785600 27583351945), (.chord (.midpoint ⟨467893634793, 122720406627, 190659482090, 356342846721, 204118447318, 227664879948⟩) 43500686443 91625974997)⟩))))
                    (.cut 2 (5/16)
                      (.original (.row ⟨106974752991, 110576703735, (.direct 30541785600 27359535713), (.variance 502957494537)⟩))
                      (.cut 2 (13/32)
                        (.original (.row ⟨106974752991, 110576703735, (.direct 30541785600 27359535713), (.chord (.midpoint ⟨413338191771, 158471709818, 211775744596, 330751393303, 224316989862, 156404123806⟩) 43500686443 65931360876)⟩))
                        (.original (.row ⟨106974752991, 110576703735, (.direct 30541785600 27359535713), (.chord (.midpoint ⟨469168797648, 121943581923, 190157913255, 357009465347, 203640621998, 226218091185⟩) 65931360876 91625974997)⟩)))))
                  (.cut 2 (5/16)
                    (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 26738654961), (.variance 505989850570)⟩))
                    (.cut 2 (13/32)
                      (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 26738654961), (.chord (.midpoint ⟨400831836449, 167391184817, 213375243583, 328990328957, 228896427480, 150111726804⟩) 43500686443 65931360876)⟩))
                      (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 26738654961), (.chord (.midpoint ⟨455245434495, 130567523661, 192204447408, 354308189158, 208841633523, 221095181377⟩) 65931360876 91625974997)⟩))))))
              (.cut 3 (-15/32)
                (.original (.row ⟨103236350715, 110576703735, (.direct 82716570280 74075313686), (.variance 387489601303)⟩))
                (.cut 2 (5/16)
                  (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 25512753545), (.variance 512246601900)⟩))
                  (.cut 3 (-23/64)
                    (.original (.row ⟨103236350715, 110576703735, (.direct 54287234842 47469861533), (.variance 435377384249)⟩))
                    (.cut 1 (7/50)
                      (.original (.row ⟨103236350715, 106974752992, (.direct 30541785600 25862093328), (.chord (.midpoint ⟨442962912322, 138438183394, 193646502774, 352434127216, 213402333159, 212749577671⟩) 43500686443 91625974997)⟩))
                      (.original (.row ⟨106974752991, 110576703735, (.direct 30541785600 25512753545), (.chord (.midpoint ⟨444963014855, 137139468021, 192852380523, 353463186594, 212661264432, 213705705616⟩) 43500686443 91625974997)⟩))))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨103236350715, 110576703735, (.direct 331294831298 310261370091), (.variance 266298918761)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨103236350715, 110576703735, (.direct 151782739331 139306251367), (.variance 328422366710)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨103236350715, 110576703735, (.direct 82716570280 74075313686), (.variance 387489601303)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutMid4H1NegRestPart0_ok : CutMid4H1NegRestPart0Tree.geometryOK CutMid4H1NegPowerCache CutMid4H1NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
