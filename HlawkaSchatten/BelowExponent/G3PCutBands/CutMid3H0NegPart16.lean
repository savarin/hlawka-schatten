/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H0NegPart16`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H0NegPart16Box : Box := (((((⟨![0, 11/100, 0, -8], ![9/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutMid3H0NegPart16Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨95281442640, 103236350716, (.direct 10180561190 8877205668), (.chord .universal 91625974997 274877906944)⟩)
      (.row ⟨95281442640, 103236350716, (.direct 0 162890367), (.chord .universal 91625974997 274877906944)⟩))
    (.cut 3 (1/8)
      (.row ⟨95281442640, 103236350716, (.direct 10180561190 11239342526), (.chord .universal 91625974997 274877906944)⟩)
      (.row ⟨95281442640, 103236350716, (.direct 30541785600 31888945087), (.chord (.secant 1184817227205 95666515910 114172333 10180561190) 91625974997 274877906944)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H0NegPart16_checked : CutMid3H0NegPart16Tree.commonOK CutMid3H0NegPart16Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
