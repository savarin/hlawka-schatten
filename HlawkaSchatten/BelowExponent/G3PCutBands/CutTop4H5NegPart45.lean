/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H5NegPart45`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H5NegPart45Box : Box := (((((((((⟨![45/136, 19/100, 0, -8], ![27/68, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)).lowerChild 2 (3/4)).lowerChild 3 (0)).lowerChild 2 (5/8)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop4H5NegPart45Tree : CertTree :=
  .cut 3 (-3/16)
    (.cut 0 (99/272)
      (.row ⟨123862991199, 126950446638, (.direct 19358451269 12111674393), (.chord (.midpoint ⟨493151483119, 107811728302, 158130748285, 406921130875, 194590511600, 309209339611⟩) 91625974997 130502050762)⟩)
      (.row ⟨123862991199, 126950446638, (.direct 19358451269 11516319167), (.chord (.midpoint ⟨479115911566, 115972613166, 160394587457, 402837745044, 199902096206, 305584481904⟩) 91625974997 130502050762)⟩))
    (.cut 0 (99/272)
      (.cut 0 (189/544)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 5175720423), (.chord (.midpoint ⟨544163383410, 80669507535, 134842717113, 455617628006, 174837498402, 329054118970⟩) 91625974997 130502050762)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 4969296443), (.chord (.midpoint ⟨536762879354, 84367813292, 136160947077, 452483538239, 177754029555, 327293092944⟩) 91625974997 130502050762)⟩))
      (.cut 0 (207/544)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 4765989837), (.chord (.midpoint ⟨529399842746, 88126946240, 137470183479, 449421753679, 180636996061, 325525318217⟩) 91625974997 130502050762)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 4565834898), (.chord (.midpoint ⟨522074409350, 91946215866, 138770632137, 446429472988, 183487679499, 323750705789⟩) 91625974997 130502050762)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop4H5NegPart45_checked : CutTop4H5NegPart45Tree.commonOK CutTop4H5NegPart45Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
