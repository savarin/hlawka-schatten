/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H4NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H4NegPart2Box : Box := (((((((((⟨![9/34, 4/25, 0, -8], ![45/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop1H4NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨114055813619, 117423580140, (.direct 19358451269 13735500580), (.variance 602415989741)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 6093389421), (.chord (.midpoint ⟨427818125975, 148490981544, 192871769871, 353437974754, 218995537389, 157935879390⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨114055813619, 117423580140, (.direct 19358451269 13735500580), (.chord (.midpoint ⟨392548256414, 173455611545, 206950590401, 336204538826, 231922727231, 215143070821⟩) 24716235638 43500686443)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 6093389421), (.chord (.midpoint ⟨493148225154, 107813587153, 165874396089, 393349528343, 194591749853, 264599610731⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H4NegPart2_checked : CutTop1H4NegPart2Tree.commonOK CutTop1H4NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
