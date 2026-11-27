/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H5NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H5NegPart2Box : Box := (((((((((⟨![45/136, 4/25, 0, -8], ![27/68, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop1H5NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨114055813619, 117423580140, (.direct 19358451269 12697978804), (.variance 614933981846)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 5371396618), (.chord (.midpoint ⟨410226710690, 160664570085, 193175996750, 353042957098, 225457625450, 155176836087⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨114055813619, 117423580140, (.direct 19358451269 12697978804), (.chord (.midpoint ⟨371486578607, 189455757636, 208857456900, 334023762350, 239599525191, 208704604193⟩) 24716235638 43500686443)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 5371396618), (.chord (.midpoint ⟨469552078806, 121710596490, 168382133602, 389184013697, 203496938306, 258782350857⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H5NegPart2_checked : CutTop1H5NegPart2Tree.commonOK CutTop1H5NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
