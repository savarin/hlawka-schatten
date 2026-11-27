/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H2NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H2NegPart1Box : Box := (((((((⟨![9/34, 13/100, 0, -8], ![27/68, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).lowerChild 3 (0)

set_option maxRecDepth 16000 in
def CutMid4H2NegPart1Tree : CertTree :=
  .cut 1 (7/50)
    (.cut 3 (-1/8)
      (.row ⟨103236350715, 106974752992, (.direct 10180561190 6196030444), (.variance 742043649290)⟩)
      (.cut 1 (27/200)
        (.cut 0 (45/136)
          (.row ⟨103236350715, 105123556200, (.direct 0 742055683), (.chord .universal 0 10180665226)⟩)
          (.cut 3 (-1/16)
            (.row ⟨103236350715, 105123556200, (.direct 3393509060 1172313288), (.chord .universal 0 10180665226)⟩)
            (.row ⟨103236350715, 105123556200, (.direct 0 990685470), (.chord .universal 0 10180665226)⟩)))
        (.cut 0 (45/136)
          (.row ⟨105123556199, 106974752992, (.direct 0 789437423), (.chord .universal 0 10180665226)⟩)
          (.cut 3 (-1/16)
            (.row ⟨105123556199, 106974752992, (.direct 3393509060 1102404381), (.chord .universal 0 10180665226)⟩)
            (.row ⟨105123556199, 106974752992, (.direct 0 1053942719), (.chord .universal 0 10180665226)⟩)))))
    (.cut 3 (-1/8)
      (.row ⟨106974752991, 110576703735, (.direct 10180561190 5919333362), (.variance 750974069599)⟩)
      (.cut 1 (29/200)
        (.cut 0 (45/136)
          (.row ⟨106974752991, 108791878640, (.direct 0 838156955), (.chord .universal 0 10180665226)⟩)
          (.row ⟨106974752991, 108791878640, (.direct 0 1118985995), (.chord .universal 0 10180665226)⟩))
        (.cut 0 (45/136)
          (.row ⟨108791878639, 110576703735, (.direct 0 888216899), (.chord .universal 0 10180665226)⟩)
          (.row ⟨108791878639, 110576703735, (.direct 0 1185818796), (.chord .universal 0 10180665226)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid4H2NegPart1_checked : CutMid4H2NegPart1Tree.commonOK CutMid4H2NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
