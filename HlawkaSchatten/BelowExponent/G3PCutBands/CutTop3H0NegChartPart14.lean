/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H0NegChartPart14`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H0NegChartPart14Box : Box := (((⟨![0, 9/50, 0, -1], ![9/136, 19/100, 1, 1]⟩ : Box)).upperChild 3 (1/4)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutTop3H0NegChartPart14Tree : RatioChart :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.row ⟨120689819474, 123862991200, (.direct 0 104337421), 0, 10180665226, 119208199333/68719476736, .leaf (.midpoint ⟨391506555903, 174227225485, 232303295731, 309737727641, 232302967313, 264086209047⟩)⟩)
      (.cut 2 (5/16)
        (.cut 2 (7/32)
          (.row ⟨120689819474, 123862991200, (.direct 6452795533 5643854742), 10180665226, 24716235638, 119208199333/68719476736, .leaf (.midpoint ⟨391506555903, 174227225485, 232303295731, 309737727641, 232302967313, 264086209047⟩)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 15665897070 14459964146), 24716235638, 43500686443, 119208199333/68719476736, .leaf (.midpoint ⟨391506555903, 174227225485, 232303295731, 309737727641, 232302967313, 264086209047⟩)⟩))
        (.cut 2 (13/32)
          (.row ⟨120689819474, 123862991200, (.direct 27572097984 25990646179), 43500686443, 65931360876, 119208199333/68719476736, .leaf (.midpoint ⟨391506555903, 174227225485, 232303295731, 309737727641, 232302967313, 264086209047⟩)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 41789416094 39836636667), 65931360876, 91625974997, 119208199333/68719476736, .leaf (.midpoint ⟨391506555903, 174227225485, 232303295731, 309737727641, 232302967313, 264086209047⟩)⟩))))
    (.cut 2 (3/4)
      (.row ⟨120689819474, 123862991200, (.direct 58075547817 55748779992), 91625974997, 174227471798, 119208199333/68719476736, .leaf (.midpoint ⟨391506555903, 174227225485, 232303295731, 309737727641, 232302967313, 264086209047⟩)⟩)
      (.row ⟨120689819474, 123862991200, (.direct 110431305439 107073283793), 174227471798, 274877906944, 119208199333/68719476736, .leaf (.midpoint ⟨391506555903, 174227225485, 232303295731, 309737727641, 232302967313, 264086209047⟩)⟩))

set_option maxRecDepth 16000 in
theorem CutTop3H0NegChartPart14_ok : CutTop3H0NegChartPart14Tree.geometryOK CutTop3H0NegPowerCache CutTop3H0NegChartPart14Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
