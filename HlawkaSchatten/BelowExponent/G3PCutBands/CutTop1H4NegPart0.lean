/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H4NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H4NegPart0Box : Box := (((⟨![9/34, 4/25, 0, -8], ![45/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop1H4NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3319821019112), (.variance 143158978140)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 765192128961), (.variance 210237786840)⟩))
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3319821019112), (.variance 143158978140)⟩)
          (.cut 3 (-7/2)
            (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1878081962571), (.variance 166188786340)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 824633666698 765192128961), (.variance 210237786840)⟩))))
      (.cut 3 (-5)
        (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3319821019112), (.variance 143158978140)⟩)
        (.cut 3 (-7/2)
          (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1878081962571), (.variance 166188786340)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 765192128961), (.variance 210237786840)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 23444205593), (.variance 523715038166)⟩)
        (.cut 3 (-9/8)
          (.row ⟨114055813619, 117423580140, (.direct 331294831298 301330100102), (.variance 268343507467)⟩)
          (.cut 3 (-11/16)
            (.row ⟨114055813619, 117423580140, (.direct 151782739331 134037500114), (.variance 331754924597)⟩)
            (.cut 3 (-15/32)
              (.row ⟨114055813619, 117423580140, (.direct 82716570280 70450736185), (.variance 392613690358)⟩)
              (.cut 2 (5/16)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 23444205593), (.variance 523715038166)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨114055813619, 117423580140, (.direct 54287234842 44629240021), (.chord (.midpoint ⟨319754105226, 232557231586, 235465091703, 306780995316, 258429156674, 129803186315⟩) 43500686443 91625974997)⟩)
                  (.row ⟨114055813619, 117423580140, (.direct 30541785600 23444205593), (.chord (.midpoint ⟨422798762136, 151909297246, 194891805806, 350834853198, 220842816078, 207676052313⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨114055813619, 117423580140, (.direct 331294831298 301330100102), (.variance 268343507467)⟩)
        (.cut 3 (-11/16)
          (.row ⟨114055813619, 117423580140, (.direct 151782739331 134037500114), (.variance 331754924597)⟩)
          (.cut 3 (-15/32)
            (.row ⟨114055813619, 117423580140, (.direct 82716570280 70450736185), (.variance 392613690358)⟩)
            (.cut 2 (3/4)
              (.row ⟨114055813619, 117423580140, (.direct 30541785600 23444205593), (.chord (.midpoint ⟨497067849960, 105589031160, 164202425408, 396187102621, 193100140165, 241105365656⟩) 91625974997 174227471798)⟩)
              (.row ⟨114055813619, 117423580140, (.direct 30541785600 23444205593), (.chord (.midpoint ⟨535842127679, 84833542109, 147228824435, 428076869363, 178115549596, 288964899934⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop1H4NegPart0_checked : CutTop1H4NegPart0Tree.commonOK CutTop1H4NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
