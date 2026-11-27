/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3NegPart11`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3NegPart11Box : Box := (((((((((((⟨![27/68, 13/100, 0, -8], ![9/17, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).upperChild 2 (5/16)).upperChild 3 (-1/8)).lowerChild 0 (63/136)).lowerChild 3 (-1/16)

set_option maxRecDepth 16000 in
def CutMid4H3NegPart11Tree : CertTree :=
  .cut 1 (7/50)
    (.cut 0 (117/272)
      (.row ⟨103236350715, 106974752992, (.direct 3393509060 955856578), (.chord (.midpoint ⟨548732641917, 78425859482, 123514524325, 484885977587, 173026812010, 316013616867⟩) 43500686443 91625974997)⟩)
      (.row ⟨103236350715, 106974752992, (.direct 3393509060 817171216), (.chord (.midpoint ⟨533185535459, 86184247761, 126677319144, 476264922537, 179156998982, 312385762361⟩) 43500686443 91625974997)⟩))
    (.cut 0 (117/272)
      (.cut 3 (-3/32)
        (.row ⟨106974752991, 110576703735, (.direct 6452795533 2819512615), (.chord (.midpoint ⟨518125634254, 94038038856, 138480768551, 447092276193, 185017425665, 317209107274⟩) 43500686443 91625974997)⟩)
        (.cut 1 (29/200)
          (.row ⟨106974752991, 108791878640, (.direct 3393509060 885431427), (.chord (.midpoint ⟨550223031612, 77700573843, 122761467880, 486994501178, 172434506113, 331086063164⟩) 43500686443 91625974997)⟩)
          (.row ⟨108791878639, 110576703735, (.direct 3393509060 816651400), (.chord (.midpoint ⟨551722981025, 76973878068, 122001022080, 489146272083, 171837539748, 331653269035⟩) 43500686443 91625974997)⟩)))
      (.cut 3 (-3/32)
        (.row ⟨106974752991, 110576703735, (.direct 6452795533 2587348171), (.chord (.midpoint ⟨503221220627, 102144195370, 141253085080, 440848485713, 190750665870, 313691347383⟩) 43500686443 91625974997)⟩)
        (.cut 1 (29/200)
          (.row ⟨106974752991, 108791878640, (.direct 3393509060 745783910), (.chord (.midpoint ⟨534773711370, 85375518445, 125880699861, 478401415458, 178534683432, 327639166088⟩) 43500686443 91625974997)⟩)
          (.row ⟨108791878639, 110576703735, (.direct 3393509060 676468330), (.chord (.midpoint ⟨536372228839, 84565258071, 125076152192, 480582760582, 177907448597, 328258180134⟩) 43500686443 91625974997)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid4H3NegPart11_checked : CutMid4H3NegPart11Tree.commonOK CutMid4H3NegPart11Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
