/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H1NegPart12`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H1NegPart12Box : Box := ((((((((((⟨![9/68, 11/100, 0, -8], ![9/34, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).upperChild 1 (3/25)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid3H1NegPart12Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨99345187399, 103236350716, (.direct 19358451269 15906611987), (.variance 579705395684)⟩)
      (.cut 2 (11/64)
        (.row ⟨99345187399, 103236350716, (.direct 10180561190 7640863183), (.chord (.midpoint ⟨396893335687, 170258811455, 218039402810, 323981447233, 230335917432, 139994717235⟩) 10180665226 16864782083)⟩)
        (.row ⟨99345187399, 103236350716, (.direct 10180561190 7640863183), (.chord (.midpoint ⟨463701060016, 125292890394, 192305565176, 354175995851, 205687293849, 223627179208⟩) 16864782083 24716235638)⟩)))
    (.cut 3 (-3/16)
      (.row ⟨99345187399, 103236350716, (.direct 19358451269 15906611987), (.chord (.midpoint ⟨435862809641, 143102649657, 203129680078, 340679382723, 216028360643, 211857463489⟩) 24716235638 43500686443)⟩)
      (.cut 0 (27/136)
        (.row ⟨99345187399, 103236350716, (.direct 10180561190 8250484876), (.chord (.midpoint ⟨532288299584, 86642774642, 164673397342, 395382813881, 179508199028, 273297064473⟩) 24716235638 43500686443)⟩)
        (.row ⟨99345187399, 103236350716, (.direct 10180561190 7640863183), (.chord (.midpoint ⟨504966846759, 101177447428, 168464797107, 389048510332, 190082355248, 266250203699⟩) 24716235638 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid3H1NegPart12_checked : CutMid3H1NegPart12Tree.commonOK CutMid3H1NegPart12Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
