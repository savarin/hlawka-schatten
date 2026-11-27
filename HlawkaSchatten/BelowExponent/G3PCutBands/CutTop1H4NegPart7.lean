/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H4NegPart7`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H4NegPart7Box : Box := (((((((((⟨![9/34, 4/25, 0, -8], ![45/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop1H4NegPart7Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 3 (-3/16)
      (.row ⟨114055813619, 117423580140, (.direct 19358451269 13735500580), (.chord (.midpoint ⟨449382859797, 134293157370, 184117225504, 365280988523, 211021482590, 268586146723⟩) 43500686443 65931360876)⟩)
      (.cut 0 (81/272)
        (.row ⟨114055813619, 117423580140, (.direct 10180561190 6466848252), (.chord (.midpoint ⟨525010269059, 90406001784, 152057451581, 418386877183, 182347231726, 304272248369⟩) 43500686443 65931360876)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 10180561190 6093389421), (.chord (.midpoint ⟨511479876900, 97611179845, 154014318882, 414608172600, 187581552623, 300944742650⟩) 43500686443 65931360876)⟩)))
    (.cut 3 (-3/16)
      (.row ⟨114055813619, 117423580140, (.direct 19358451269 13735500580), (.chord (.midpoint ⟨486325665958, 111742245283, 168768064639, 388552361119, 197179264974, 294416509199⟩) 65931360876 91625974997)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 6093389421), (.chord (.midpoint ⟨553075582635, 76321354804, 139382715816, 445037625482, 171298467218, 316834076780⟩) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H4NegPart7_checked : CutTop1H4NegPart7Tree.commonOK CutTop1H4NegPart7Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
