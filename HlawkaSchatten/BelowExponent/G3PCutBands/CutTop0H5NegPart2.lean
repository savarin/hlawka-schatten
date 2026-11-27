/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H5NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H5NegPart2Box : Box := (((((((((⟨![45/136, 3/20, 0, -8], ![27/68, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop0H5NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨110576703734, 114055813620, (.direct 19358451269 13092447035), (.variance 610027435013)⟩)
      (.row ⟨110576703734, 114055813620, (.direct 10180561190 5644399201), (.chord (.midpoint ⟨404117904212, 165020262607, 195669410052, 349845049810, 227694477916, 150674975774⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨110576703734, 114055813620, (.direct 19358451269 13092447035), (.chord (.midpoint ⟨367132540996, 192870365581, 210603359004, 332056709997, 241184338185, 206524774227⟩) 24716235638 43500686443)⟩)
      (.row ⟨110576703734, 114055813620, (.direct 10180561190 5644399201), (.chord (.midpoint ⟨465052897824, 124460342263, 170307198876, 386057625976, 205181801729, 257006843048⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H5NegPart2_checked : CutTop0H5NegPart2Tree.commonOK CutTop0H5NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
