/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2NegPart13`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H2NegPart13Box : Box := ((((((((((⟨![9/34, 11/100, 0, -8], ![27/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 1 (3/25)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutMid3H2NegPart13Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨95281442640, 99345187400, (.direct 19358451269 14670302654), (.variance 592118629662)⟩)
      (.row ⟨95281442640, 99345187400, (.direct 10180561190 6754088611), (.chord (.midpoint ⟨413677722381, 158233462527, 198547485536, 346239328584, 224192465082, 121966847217⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨95281442640, 99345187400, (.direct 19358451269 14670302654), (.chord (.midpoint ⟨382412818191, 181049670972, 210953936302, 331665082851, 235619654869, 193370524279⟩) 24716235638 43500686443)⟩)
      (.row ⟨95281442640, 99345187400, (.direct 10180561190 6754088611), (.chord (.midpoint ⟨482693624431, 113863201672, 170300286390, 386068744008, 198552374807, 246393462185⟩) 24716235638 43500686443)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H2NegPart13_checked : CutMid3H2NegPart13Tree.commonOK CutMid3H2NegPart13Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
