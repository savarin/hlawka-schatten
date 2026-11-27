/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H3NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H3NegPart2Box : Box := (((((((((⟨![27/136, 3/20, 0, -8], ![9/34, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop0H3NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨110576703734, 114055813620, (.direct 19358451269 15080465389), (.variance 587858471720)⟩)
      (.row ⟨110576703734, 114055813620, (.direct 10180561190 7046737129), (.chord (.midpoint ⟨441477333495, 139407134209, 194235699432, 351675269753, 213952380363, 158037751599⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨110576703734, 114055813620, (.direct 19358451269 15080465389), (.chord (.midpoint ⟨411011834681, 160109615925, 206211565037, 337058982827, 225169894170, 220195726172⟩) 24716235638 43500686443)⟩)
      (.row ⟨110576703734, 114055813620, (.direct 10180561190 7046737129), (.chord (.midpoint ⟨514058273599, 96217023429, 164652400617, 395418586663, 186588251263, 269295805704⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H3NegPart2_checked : CutTop0H3NegPart2Tree.commonOK CutTop0H3NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
