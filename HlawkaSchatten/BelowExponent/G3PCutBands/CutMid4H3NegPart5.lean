/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3NegPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3NegPart5Box : Box := ((((((((((⟨![27/68, 13/100, 0, -8], ![9/17, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 2 (5/16)).upperChild 1 (7/50)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid4H3NegPart5Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨106974752991, 110576703735, (.direct 19358451269 11708192971), (.variance 628141753404)⟩)
      (.row ⟨106974752991, 110576703735, (.direct 10180561190 4695304191), (.chord (.midpoint ⟨392634613641, 173391735222, 193593916478, 352502047764, 231891202120, 123450610471⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨106974752991, 110576703735, (.direct 19358451269 11708192971), (.chord (.midpoint ⟨350661950991, 206131024732, 210831353553, 331801892499, 247176464697, 182931486511⟩) 24716235638 43500686443)⟩)
      (.row ⟨106974752991, 110576703735, (.direct 10180561190 4695304191), (.chord (.midpoint ⟨446184041791, 136349903374, 170950832222, 385025775553, 212208559253, 236924089813⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutMid4H3NegPart5_checked : CutMid4H3NegPart5Tree.commonOK CutMid4H3NegPart5Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
