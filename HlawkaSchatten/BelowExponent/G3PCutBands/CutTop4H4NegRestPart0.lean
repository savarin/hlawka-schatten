/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H4NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H4NegRestPart0Box : Box := (((⟨![9/34, 19/100, 0, -8], ![45/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop4H4NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4985898697517), (.variance 128696679611)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3280394944815), (.variance 143607538224)⟩)))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 753729708479), (.variance 211070336993)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4985898697517), (.variance 128696679611)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3280394944815), (.variance 143607538224)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1854123163513), (.variance 166748453022)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 753729708479), (.variance 211070336993)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 5340438828596 4985898697517), (.variance 128696679611)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 3523554676644 3280394944815), (.variance 143607538224)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨123862991199, 126950446638, (.direct 2002014560937 1854123163513), (.variance 166748453022)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 824633666698 753729708479), (.variance 211070336993)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 22134945184), (.variance 531655477475)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 295578260255), (.variance 269701170417)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 130654172323), (.variance 333983348592)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 68131616091), (.variance 396070094035)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 22134945184), (.variance 531655477475)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨123862991199, 126950446638, (.direct 54287234842 42818276306), (.chord (.midpoint ⟨327335585276, 225881370044, 232511392434, 309541015562, 255665987629, 135841332241⟩) 43500686443 91625974997)⟩))
                  (.cut 0 (81/272)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 22930293116), (.chord (.midpoint ⟨425803789301, 149857560364, 193683175011, 352386779952, 219737231370, 218053917594⟩) 43500686443 91625974997)⟩))
                    (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 22134945184), (.chord (.midpoint ⟨413632433134, 158265229994, 195194677512, 350448529923, 224209075826, 214627576849⟩) 43500686443 91625974997)⟩)))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨123862991199, 126950446638, (.direct 331294831298 295578260255), (.variance 269701170417)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 130654172323), (.variance 333983348592)⟩))
          (.cut 3 (-15/32)
            (.cut 2 (3/4)
              (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 68131616091), (.chord (.midpoint ⟨358431355602, 199807227239, 220372179406, 321544386938, 244350239680, 157962177673⟩) 91625974997 174227471798)⟩))
              (.covered))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop4H4NegRestPart0_ok : CutTop4H4NegRestPart0Tree.ok CutTop4H4NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
