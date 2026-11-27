/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3NegPart2Box : Box := ((((((((((⟨![27/68, 13/100, 0, -8], ![9/17, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 2 (5/16)).lowerChild 1 (7/50)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid4H3NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨103236350715, 106974752992, (.direct 19358451269 12208733601), (.variance 621293571518)⟩)
      (.row ⟨103236350715, 106974752992, (.direct 10180561190 5035545832), (.chord (.midpoint ⟨384799543799, 179243949920, 196837784512, 348370416582, 234749598387, 117182843060⟩) 10180665226 24716235638)⟩))
    (.cut 0 (63/136)
      (.row ⟨103236350715, 106974752992, (.direct 10180561190 5604696732), (.chord (.midpoint ⟨431166193933, 146235008001, 177398483294, 375043629309, 217761653621, 194095952559⟩) 24716235638 43500686443)⟩)
      (.row ⟨103236350715, 106974752992, (.direct 10180561190 5035545832), (.chord (.midpoint ⟨406613200041, 163232958171, 180701841124, 370166154307, 226781174340, 185758542173⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutMid4H3NegPart2_checked : CutMid4H3NegPart2Tree.commonOK CutMid4H3NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
