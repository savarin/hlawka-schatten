/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H5NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H5NegPart1Box : Box := ((((((⟨![45/136, 3/20, 0, -8], ![27/68, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop0H5NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨110576703734, 114055813620, (.direct 10180561190 5644399201), (.variance 760385228311)⟩)
      (.row ⟨110576703734, 114055813620, (.direct 0 1324871185), (.chord .universal 0 10180665226)⟩))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.cut 1 (31/200)
            (.cut 1 (61/400)
              (.cut 0 (99/272)
                (.cut 2 (1/16)
                  (.row ⟨110576703734, 111457516073, (.direct 1131165907 3210797900), (.variance 1234050008103)⟩)
                  (.row ⟨110576703734, 111457516073, (.direct 1131165907 3210797900), (.chord (.secant 1276466221019 133757568164 13497689066 23981670171) 3393555298 10180665226)⟩))
                (.cut 2 (1/16)
                  (.row ⟨110576703734, 111457516073, (.direct 1131165907 3436737176), (.variance 1186187214892)⟩)
                  (.row ⟨110576703734, 111457516073, (.direct 1131165907 3436737176), (.chord (.secant 1283573079051 136858542577 15200557250 27892373940) 3393555298 10180665226)⟩)))
              (.cut 0 (99/272)
                (.cut 2 (1/16)
                  (.row ⟨111457516072, 112330851340, (.direct 1131165907 3254517259), (.variance 1224925379245)⟩)
                  (.row ⟨111457516072, 112330851340, (.direct 1131165907 3254517259), (.chord (.secant 1282826393466 136531804404 12947199260 24671074767) 3393555298 10180665226)⟩))
                (.cut 2 (1/16)
                  (.row ⟨111457516072, 112330851340, (.direct 1131165907 3485648685), (.variance 1177416485975)⟩)
                  (.row ⟨111457516072, 112330851340, (.direct 1131165907 3485648685), (.chord (.secant 1290526236569 139911559643 14567974573 28694200111) 3393555298 10180665226)⟩))))
            (.cut 1 (63/400)
              (.cut 0 (99/272)
                (.row ⟨112330851339, 113196892094, (.direct 1131165907 3298573984), (.chord .universal 0 10180665226)⟩)
                (.cut 3 (1/64)
                  (.row ⟨112330851339, 113196892094, (.direct 377054043 2310225281), (.chord .universal 0 10180665226)⟩)
                  (.row ⟨112330851339, 113196892094, (.direct 1131165907 3534948592), (.variance 989071275577)⟩)))
              (.cut 0 (99/272)
                (.row ⟨113196892093, 114055813620, (.direct 1131165907 3342969572), (.chord .universal 0 10180665226)⟩)
                (.row ⟨113196892093, 114055813620, (.direct 1131165907 3584638581), (.chord .universal 0 10180665226)⟩))))
          (.cut 3 (3/64)
            (.cut 2 (1/16)
              (.row ⟨110576703734, 114055813620, (.direct 2150924658 4997036953), (.variance 901034588787)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 2150924658 4997036953), (.chord (.secant 1523270818042 251579319105 3253548229 79707911157) 3393555298 10180665226)⟩))
            (.row ⟨110576703734, 114055813620, (.direct 3393509060 6575364047), (.variance 817104122789)⟩)))
        (.cut 3 (3/32)
          (.row ⟨110576703734, 114055813620, (.direct 6452795533 10185824267), (.variance 754978158433)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 10180561190 14347703660), (.variance 667186518960)⟩)))
      (.cut 3 (3/16)
        (.row ⟨110576703734, 114055813620, (.direct 19358451269 24146173318), (.variance 606645711740)⟩)
        (.row ⟨110576703734, 114055813620, (.direct 30541785600 35705916189), (.variance 526075248527)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop0H5NegPart1_checked : CutTop0H5NegPart1Tree.commonOK CutTop0H5NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
