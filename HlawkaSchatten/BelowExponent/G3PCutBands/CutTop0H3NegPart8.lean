/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H3NegPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H3NegPart8Box : Box := (((((⟨![27/136, 3/20, 0, -8], ![9/34, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop0H3NegPart8Tree : CertTree :=
  .cut 3 (0)
    (.cut 2 (3/4)
      (.cut 3 (-1/8)
        (.row ⟨110576703734, 114055813620, (.direct 10180561190 7046737129), (.chord (.midpoint ⟨619244655158, 47576739622, 116767304327, 504602525351, 143880156176, 316932091012⟩) 91625974997 174227471798)⟩)
        (.cut 3 (-1/16)
          (.row ⟨110576703734, 114055813620, (.direct 3393509060 1545031550), (.chord (.midpoint ⟨667790979950, 30397472608, 90607917112, 604095697459, 121953776382, 351369560023⟩) 91625974997 174227471798)⟩)
          (.cut 3 (-1/32)
            (.row ⟨110576703734, 114055813620, (.direct 1131165907 118131159), (.chord (.midpoint ⟨692567895730, 22913876265, 75288104712, 688935713907, 109874202799, 367715183487⟩) 91625974997 174227471798)⟩)
            (.cut 3 (-1/64)
              (.row ⟨110576703734, 114055813620, (.direct 377054043 124162230), (.chord (.secant 708271415556 18631177339 39491539714 1021350131) 91625974997 174227471798)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 0 696747837), (.chord (.secant 727226764627 13951482776 33245184691 4565320) 91625974997 174227471798)⟩)))))
      (.row ⟨110576703734, 114055813620, (.direct 0 696747837), (.chord .universal 174227471798 274877906944)⟩))
    (.cut 2 (3/4)
      (.cut 3 (1/8)
        (.cut 3 (1/16)
          (.cut 3 (1/32)
            (.cut 0 (63/272)
              (.row ⟨110576703734, 114055813620, (.direct 1131165907 2440380061), (.chord (.secant 762146915744 6811690708 23194808822 623608613) 91625974997 174227471798)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 1131165907 2656154377), (.chord (.secant 744755902774 10118728421 28565362437 796197077) 91625974997 174227471798)⟩))
            (.row ⟨110576703734, 114055813620, (.direct 3393509060 5430156320), (.chord (.secant 804877136492 1081144025 21826796863 3389946819) 91625974997 174227471798)⟩))
          (.row ⟨110576703734, 114055813620, (.direct 10180561190 12900516063), (.chord (.secant 885396885303 6236181594 15242715558 7543105683) 91625974997 174227471798)⟩))
        (.row ⟨110576703734, 114055813620, (.direct 30541785600 33951622916), (.chord (.secant 1054766891127 48797528849 4945119232 19023490522) 91625974997 174227471798)⟩))
      (.row ⟨110576703734, 114055813620, (.direct 30541785600 33951622916), (.chord .universal 174227471798 274877906944)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H3NegPart8_checked : CutTop0H3NegPart8Tree.commonOK CutTop0H3NegPart8Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
