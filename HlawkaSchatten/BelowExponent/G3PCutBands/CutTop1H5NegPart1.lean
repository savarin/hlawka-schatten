/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H5NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H5NegPart1Box : Box := ((((((⟨![45/136, 4/25, 0, -8], ![27/68, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop1H5NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 5371396618), (.variance 770320825741)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 0 1471144105), (.chord .universal 0 10180665226)⟩))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.cut 1 (33/200)
            (.cut 1 (13/80)
              (.cut 0 (99/272)
                (.row ⟨114055813619, 114907784327, (.direct 1131165907 3387705530), (.chord .universal 0 10180665226)⟩)
                (.row ⟨114055813619, 114907784327, (.direct 1131165907 3634720350), (.chord .universal 0 10180665226)⟩))
              (.row ⟨114907784326, 115752966124, (.direct 1131165907 3685195615), (.chord .universal 0 10180665226)⟩))
            (.cut 0 (99/272)
              (.row ⟨115752966123, 117423580140, (.direct 1131165907 3523970925), (.chord .universal 0 10180665226)⟩)
              (.row ⟨115752966123, 117423580140, (.direct 1131165907 3787333580), (.chord .universal 0 10180665226)⟩)))
          (.cut 3 (3/64)
            (.row ⟨114055813619, 117423580140, (.direct 2150924658 5222012418), (.variance 889009375189)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 3393509060 6819900110), (.variance 808583993960)⟩)))
        (.cut 3 (3/32)
          (.row ⟨114055813619, 117423580140, (.direct 6452795533 10463150509), (.variance 748556937686)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 10180561190 14651222273), (.variance 663097419414)⟩)))
      (.cut 3 (3/16)
        (.row ⟨114055813619, 117423580140, (.direct 19358451269 24487270960), (.variance 603784238379)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 36069416821), (.variance 524436182102)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop1H5NegPart1_checked : CutTop1H5NegPart1Tree.commonOK CutTop1H5NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
