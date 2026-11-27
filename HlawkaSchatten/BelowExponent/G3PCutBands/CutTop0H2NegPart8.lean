/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H2NegPart8`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H2NegPart8Box : Box := (((((⟨![9/68, 3/20, 0, -8], ![27/136, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop0H2NegPart8Tree : CertTree :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.cut 3 (-3/16)
        (.row ⟨110576703734, 114055813620, (.direct 19358451269 16112886410), (.chord (.midpoint ⟨637758011706, 40635640785, 117289415485, 503007769167, 135745064078, 324536275844⟩) 91625974997 274877906944)⟩)
        (.row ⟨110576703734, 114055813620, (.direct 10180561190 7790128701), (.chord (.midpoint ⟨674648998488, 28238185668, 98082326950, 571059132057, 118681954679, 341882425121⟩) 91625974997 274877906944)⟩))
      (.cut 3 (-1/16)
        (.row ⟨110576703734, 114055813620, (.direct 3393509060 1956701448), (.chord (.midpoint ⟨712300039129, 17591219964, 75711348869, 686200939547, 99661011635, 358625275733⟩) 91625974997 274877906944)⟩)
        (.cut 3 (-1/32)
          (.row ⟨110576703734, 114055813620, (.direct 1131165907 297225525), (.chord (.midpoint ⟨731407205012, 12993405430, 62559098924, 785685767356, 89117987527, 374830887340⟩) 91625974997 274877906944)⟩)
          (.cut 3 (-1/64)
            (.row ⟨110576703734, 114055813620, (.direct 377054043 13459207), (.chord (.secant 742229753028 10640853612 28420025972 1697193822) 91625974997 274877906944)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 0 441623758), (.chord (.secant 761626962575 6903089402 22815729760 169985391) 91625974997 274877906944)⟩)))))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 3 (1/32)
          (.row ⟨110576703734, 114055813620, (.direct 1131165907 2231428794), (.chord (.secant 800972360175 1440880833 19407413276 207868843) 91625974997 274877906944)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 3393509060 4888384789), (.chord (.secant 841044400127 794999910 14593511745 1783232844) 91625974997 274877906944)⟩))
        (.row ⟨110576703734, 114055813620, (.direct 10180561190 12198414438), (.chord (.secant 923331867962 13285297310 10306008608 4299204000) 91625974997 274877906944)⟩))
      (.row ⟨110576703734, 114055813620, (.direct 30541785600 33086761949), (.chord (.secant 1096244869676 62692313238 3535727493 11419036295) 91625974997 274877906944)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H2NegPart8_checked : CutTop0H2NegPart8Tree.commonOK CutTop0H2NegPart8Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
