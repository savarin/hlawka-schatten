/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H4NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H4NegPart1Box : Box := ((((((⟨![9/34, 4/25, 0, -8], ![45/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop1H4NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 6093389421), (.variance 745296602371)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 0 1101934848), (.chord .universal 0 10180665226)⟩))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.cut 1 (33/200)
            (.cut 1 (13/80)
              (.row ⟨114055813619, 114907784327, (.direct 1131165907 3147166676), (.chord .universal 0 10180665226)⟩)
              (.row ⟨114907784326, 115752966124, (.direct 1131165907 3187042989), (.chord .universal 0 10180665226)⟩))
            (.row ⟨115752966123, 117423580140, (.direct 1131165907 3267680649), (.chord .universal 0 10180665226)⟩))
          (.cut 2 (1/16)
            (.row ⟨114055813619, 117423580140, (.direct 3393509060 6189423888), (.variance 926311762522)⟩)
            (.cut 2 (3/32)
              (.row ⟨114055813619, 117423580140, (.direct 3393509060 6189423888), (.chord (.secant 1733814141719 365214335964 28685697357 113145945715) 3393555298 6452870597)⟩)
              (.row ⟨114055813619, 117423580140, (.direct 3393509060 6189423888), (.chord (.secant 1334178078095 159494940563 6867446694 71715855290) 6452870597 10180665226)⟩))))
        (.cut 3 (3/32)
          (.cut 3 (5/64)
            (.row ⟨114055813619, 117423580140, (.direct 4833349683 7893606904), (.variance 768129286434)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 6452795533 9746039586), (.variance 716741602741)⟩))
          (.row ⟨114055813619, 117423580140, (.direct 10180561190 13864979952), (.variance 675457301012)⟩)))
      (.cut 3 (3/16)
        (.row ⟨114055813619, 117423580140, (.direct 19358451269 23601850545), (.variance 612391095092)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 35124742663), (.variance 529339168742)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop1H4NegPart1_checked : CutTop1H4NegPart1Tree.commonOK CutTop1H4NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
