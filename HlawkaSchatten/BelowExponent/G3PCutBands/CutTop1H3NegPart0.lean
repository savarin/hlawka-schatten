/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H3NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H3NegPart0Box : Box := (((⟨![27/136, 4/25, 0, -8], ![9/34, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop1H3NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3360214423855), (.variance 142706330707)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 776949445600), (.variance 209400009929)⟩))
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3360214423855), (.variance 142706330707)⟩)
          (.cut 3 (-7/2)
            (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1902636697706), (.variance 165624470427)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 824633666698 776949445600), (.variance 209400009929)⟩))))
      (.cut 3 (-5)
        (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3360214423855), (.variance 142706330707)⟩)
        (.cut 3 (-7/2)
          (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1902636697706), (.variance 165624470427)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 776949445600), (.variance 209400009929)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 24808041560), (.variance 516017665225)⟩)
        (.cut 3 (-9/8)
          (.row ⟨114055813619, 117423580140, (.direct 331294831298 307239017799), (.variance 266982404468)⟩)
          (.cut 3 (-11/16)
            (.row ⟨114055813619, 117423580140, (.direct 151782739331 137521270936), (.variance 329533317736)⟩)
            (.cut 3 (-15/32)
              (.row ⟨114055813619, 117423580140, (.direct 82716570280 72845623062), (.variance 389191889334)⟩)
              (.cut 2 (5/16)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 24808041560), (.variance 516017665225)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨114055813619, 117423580140, (.direct 54287234842 46504790198), (.chord (.midpoint ⟨342838472817, 212625401291, 232513438631, 309539082804, 250022548022, 140223362918⟩) 43500686443 91625974997)⟩)
                  (.row ⟨114055813619, 117423580140, (.direct 30541785600 24808041560), (.chord (.midpoint ⟨449039038035, 134513411773, 191230901615, 355587035705, 211149151196, 215639849276⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨114055813619, 117423580140, (.direct 331294831298 307239017799), (.variance 266982404468)⟩)
        (.cut 3 (-11/16)
          (.row ⟨114055813619, 117423580140, (.direct 151782739331 137521270936), (.variance 329533317736)⟩)
          (.cut 3 (-15/32)
            (.row ⟨114055813619, 117423580140, (.direct 82716570280 72845623062), (.variance 389191889334)⟩)
            (.cut 2 (3/4)
              (.cut 3 (-23/64)
                (.row ⟨114055813619, 117423580140, (.direct 54287234842 46504790198), (.chord (.midpoint ⟨451091703969, 133201357174, 190412699466, 356670462250, 210386671365, 249692285381⟩) 91625974997 174227471798)⟩)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 24808041560), (.chord (.midpoint ⟨527729741365, 88990702820, 158846435732, 405619462627, 181288418744, 284954330939⟩) 91625974997 174227471798)⟩))
              (.row ⟨114055813619, 117423580140, (.direct 30541785600 24808041560), (.chord (.midpoint ⟨568808685072, 68924484868, 140766421954, 441929323189, 164973319811, 297398954920⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop1H3NegPart0_checked : CutTop1H3NegPart0Tree.commonOK CutTop1H3NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
