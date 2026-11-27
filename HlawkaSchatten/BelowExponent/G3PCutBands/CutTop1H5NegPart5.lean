/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H5NegPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H5NegPart5Box : Box := (((((((((⟨![45/136, 4/25, 0, -8], ![27/68, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).upperChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop1H5NegPart5Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 3 (-3/16)
      (.row ⟨114055813619, 117423580140, (.direct 19358451269 12697978804), (.chord (.midpoint ⟨424464485610, 150770060078, 187327852505, 360827894678, 220230106312, 261464367409⟩) 43500686443 65931360876)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 5371396618), (.chord (.midpoint ⟨502706384138, 102430202158, 153897911494, 414830655921, 190947616240, 292531405864⟩) 43500686443 65931360876)⟩))
    (.cut 0 (99/272)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 5728193919), (.chord (.midpoint ⟨520031307689, 93025627811, 146082425322, 430457683423, 184279762009, 292054047740⟩) 65931360876 91625974997)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 5371396618), (.chord (.midpoint ⟨505677772403, 100785054057, 148492718743, 425488505204, 189809945166, 288304120987⟩) 65931360876 91625974997)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H5NegPart5_checked : CutTop1H5NegPart5Tree.commonOK CutTop1H5NegPart5Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
