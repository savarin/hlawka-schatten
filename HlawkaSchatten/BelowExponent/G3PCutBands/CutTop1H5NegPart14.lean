/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H5NegPart14`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H5NegPart14Box : Box := ((⟨![45/136, 4/25, 0, -8], ![27/68, 17/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop1H5NegPart14Tree : CertTree :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cone)
          (.row ⟨114055813619, 117423580140, .zero, (.variance 308513106492)⟩))
        (.row ⟨114055813619, 117423580140, .zero, (.variance 308513106492)⟩))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.row ⟨114055813619, 117423580140, (.direct 391506126583 386938798882), (.variance 251335380321)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 593382169971 580096620026), (.variance 226049837517)⟩))
          (.row ⟨114055813619, 117423580140, (.direct 391506126583 386938798882), (.variance 251335380321)⟩))
        (.row ⟨114055813619, 117423580140, (.direct 391506126583 386938798882), (.variance 251335380321)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨114055813619, 117423580140, (.direct 824633666698 800661924032), (.variance 207758021928)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1919071833634), (.variance 165251867789)⟩))
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3360214423855), (.variance 142706330707)⟩))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨114055813619, 117423580140, (.direct 824633666698 800661924032), (.variance 207758021928)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1919071833634), (.variance 165251867789)⟩))
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3360214423855), (.variance 142706330707)⟩)))
      (.row ⟨114055813619, 117423580140, (.direct 824633666698 800661924032), (.variance 207758021928)⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H5NegPart14_checked : CutTop1H5NegPart14Tree.commonOK CutTop1H5NegPart14Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
