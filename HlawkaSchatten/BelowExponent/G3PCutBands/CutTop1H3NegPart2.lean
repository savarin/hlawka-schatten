/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H3NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H3NegPart2Box : Box := (((((((((⟨![27/136, 4/25, 0, -8], ![9/34, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop1H3NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨114055813619, 117423580140, (.direct 19358451269 14802791286), (.variance 590726268545)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 6848442653), (.chord (.midpoint ⟨445680660238, 136675109361, 192567202135, 353834503389, 212395219322, 160661140559⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨114055813619, 117423580140, (.direct 19358451269 14802791286), (.chord (.midpoint ⟨414035534625, 157982608307, 205031175272, 338434634604, 224061223120, 221447629139⟩) 24716235638 43500686443)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 6848442653), (.chord (.midpoint ⟨517168641432, 94548496801, 163339464951, 397671078866, 185387456740, 270327508170⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H3NegPart2_checked : CutTop1H3NegPart2Tree.commonOK CutTop1H3NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
