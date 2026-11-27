/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3NegPart10`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3NegPart10Box : Box := (((((((((⟨![27/68, 13/100, 0, -8], ![9/17, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).upperChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid4H3NegPart10Tree : CertTree :=
  .cut 0 (63/136)
    (.cut 2 (13/32)
      (.cut 1 (7/50)
        (.row ⟨103236350715, 106974752992, (.direct 10180561190 5604696732), (.chord (.midpoint ⟨464201412790, 124984398079, 163089575493, 398103302613, 205500236693, 249463497100⟩) 43500686443 65931360876)⟩)
        (.row ⟨106974752991, 110576703735, (.direct 10180561190 5294254112), (.chord (.midpoint ⟨468149022501, 122564617005, 161346640371, 401149778667, 204022774340, 251033090487⟩) 43500686443 65931360876)⟩))
      (.cut 1 (7/50)
        (.row ⟨103236350715, 106974752992, (.direct 10180561190 5604696732), (.chord (.midpoint ⟨485302194066, 112337826557, 153676625098, 415254383216, 197566493594, 275891582056⟩) 65931360876 91625974997)⟩)
        (.row ⟨106974752991, 110576703735, (.direct 10180561190 5294254112), (.chord (.midpoint ⟨488561614008, 110446765122, 152200048708, 418108718491, 196332463868, 277016583160⟩) 65931360876 91625974997)⟩)))
    (.cut 2 (13/32)
      (.cut 1 (7/50)
        (.row ⟨103236350715, 106974752992, (.direct 10180561190 5035545832), (.chord (.midpoint ⟨436816894215, 142470912792, 167539853743, 390571204522, 215675895271, 241135291707⟩) 43500686443 65931360876)⟩)
        (.row ⟨106974752991, 110576703735, (.direct 10180561190 4695304191), (.chord (.midpoint ⟨441229623214, 139569059950, 165584930325, 393837286240, 214044065776, 243010151162⟩) 43500686443 65931360876)⟩))
      (.row ⟨103236350715, 110576703735, (.direct 10180561190 4695304191), (.chord (.midpoint ⟨459738491778, 127750294071, 157280017555, 408481573334, 207167089837, 267456948735⟩) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutMid4H3NegPart10_checked : CutMid4H3NegPart10Tree.commonOK CutMid4H3NegPart10Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
