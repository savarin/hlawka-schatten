/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H7NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H7NegPart2Box : Box := ((((((((⟨![63/136, 4/25, 0, -8], ![9/17, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop1H7NegPart2Tree : CertTree :=
  .cut 2 (5/16)
    (.cut 2 (7/32)
      (.cut 3 (-3/16)
        (.row ⟨114055813619, 117423580140, (.direct 19358451269 10714764060), (.variance 642896642040)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 10180561190 4031178183), (.chord (.midpoint ⟨375869344623, 186056144626, 193783433116, 352257415613, 238003666117, 149551402605⟩) 10180665226 24716235638)⟩))
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 4031178183), (.chord (.midpoint ⟨423654779510, 151323240022, 173319848680, 381284363886, 220527983562, 195383640622⟩) 24716235638 43500686443)⟩))
    (.cut 2 (13/32)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 4031178183), (.chord (.midpoint ⟨450250109052, 133738459641, 161559564972, 400774596337, 210699370322, 246789746277⟩) 43500686443 65931360876)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 4031178183), (.chord (.midpoint ⟨467173852543, 123160044683, 153891161323, 414843565991, 204388023743, 271510068923⟩) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H7NegPart2_checked : CutTop1H7NegPart2Tree.commonOK CutTop1H7NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
