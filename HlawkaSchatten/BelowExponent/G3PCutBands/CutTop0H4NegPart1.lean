/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H4NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H4NegPart1Box : Box := ((((((⟨![9/34, 3/20, 0, -8], ![45/136, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop0H4NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨110576703734, 114055813620, (.direct 10180561190 6331229389), (.variance 737861156740)⟩)
      (.row ⟨110576703734, 114055813620, (.direct 0 992371667), (.chord .universal 0 10180665226)⟩))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 1 (31/200)
          (.cut 3 (1/32)
            (.cut 1 (61/400)
              (.cut 0 (81/272)
                (.row ⟨110576703734, 111457516073, (.direct 1131165907 2776191740), (.chord .universal 0 10180665226)⟩)
                (.cut 2 (1/16)
                  (.row ⟨110576703734, 111457516073, (.direct 1131165907 2990580254), (.chord .universal 0 3393555298)⟩)
                  (.row ⟨110576703734, 111457516073, (.direct 1131165907 2990580254), (.chord (.secant 1269373936590 130682903020 11870676737 20293422556) 3393555298 10180665226)⟩)))
              (.cut 0 (81/272)
                (.row ⟨111457516072, 112330851340, (.direct 1131165907 2810083961), (.chord .universal 0 10180665226)⟩)
                (.row ⟨111457516072, 112330851340, (.direct 1131165907 3029291681), (.chord .universal 0 10180665226)⟩)))
            (.cut 2 (1/16)
              (.row ⟨110576703734, 112330851340, (.direct 3393509060 5895949099), (.variance 937349232999)⟩)
              (.row ⟨110576703734, 112330851340, (.direct 3393509060 5895949099), (.chord (.secant 1696052888265 344108066101 5571454595 68544095922) 3393555298 10180665226)⟩)))
          (.cut 3 (1/32)
            (.cut 1 (63/400)
              (.cut 0 (81/272)
                (.row ⟨112330851339, 113196892094, (.direct 1131165907 2844220314), (.chord .universal 0 10180665226)⟩)
                (.row ⟨112330851339, 113196892094, (.direct 1131165907 3068292350), (.chord .universal 0 10180665226)⟩))
              (.row ⟨113196892093, 114055813620, (.direct 1131165907 3107583574), (.chord .universal 0 10180665226)⟩))
            (.cut 2 (1/16)
              (.row ⟨112330851339, 114055813620, (.direct 3393509060 5992658979), (.variance 931789736508)⟩)
              (.row ⟨112330851339, 114055813620, (.direct 3393509060 5992658979), (.chord (.secant 1708537548993 351053830168 6205203554 70119059175) 3393555298 10180665226)⟩))))
        (.cut 3 (3/32)
          (.cut 3 (5/64)
            (.row ⟨110576703734, 114055813620, (.direct 4833349683 7681752703), (.variance 773726588874)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 6452795533 9520767976), (.variance 721079162518)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 10180561190 13617013264), (.variance 678935183428)⟩)))
      (.cut 3 (3/16)
        (.cut 3 (5/32)
          (.row ⟨110576703734, 114055813620, (.direct 14500097491 18229969881), (.variance 614790107866)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 19358451269 23321333133), (.variance 567503878281)⟩))
        (.row ⟨110576703734, 114055813620, (.direct 30541785600 34824692462), (.variance 530691378791)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop0H4NegPart1_checked : CutTop0H4NegPart1Tree.commonOK CutTop0H4NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
