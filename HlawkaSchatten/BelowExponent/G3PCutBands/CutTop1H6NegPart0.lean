/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H6NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H6NegPart0Box : Box := (((⟨![27/68, 4/25, 0, -8], ![63/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop1H6NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3239576536155), (.variance 144079163886)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 741876661933), (.variance 211948231976)⟩))
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3239576536155), (.variance 144079163886)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 741876661933), (.variance 211948231976)⟩)))
      (.cut 3 (-5)
        (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3239576536155), (.variance 144079163886)⟩)
        (.cut 3 (-7/2)
          (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1829326653736), (.variance 167337380682)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 741876661933), (.variance 211948231976)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 20803000397), (.variance 540366050785)⟩)
        (.cut 3 (-9/8)
          (.row ⟨114055813619, 117423580140, (.direct 331294831298 289639860048), (.variance 271138300048)⟩)
          (.cut 3 (-11/16)
            (.row ⟨114055813619, 117423580140, (.direct 151782739331 127169492742), (.variance 336355966855)⟩)
            (.cut 3 (-15/32)
              (.row ⟨114055813619, 117423580140, (.direct 82716570280 65750260163), (.variance 399777272056)⟩)
              (.cut 2 (5/16)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 20803000397), (.variance 540366050785)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨114055813619, 117423580140, (.direct 54287234842 40964408904), (.chord (.midpoint ⟨275395040419, 274361132288, 241291097215, 301506828145, 274687066571, 106916327641⟩) 43500686443 91625974997)⟩)
                  (.row ⟨114055813619, 117423580140, (.direct 30541785600 20803000397), (.chord (.midpoint ⟨372091271494, 188984481762, 202071239820, 341944519234, 239379381738, 191057040804⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨114055813619, 117423580140, (.direct 331294831298 289639860048), (.variance 271138300048)⟩)
        (.cut 3 (-11/16)
          (.row ⟨114055813619, 117423580140, (.direct 151782739331 127169492742), (.variance 336355966855)⟩)
          (.cut 3 (-15/32)
            (.row ⟨114055813619, 117423580140, (.direct 82716570280 65750260163), (.variance 399777272056)⟩)
            (.cut 2 (3/4)
              (.row ⟨114055813619, 117423580140, (.direct 30541785600 20803000397), (.chord (.midpoint ⟨437803490632, 141819268098, 174559682419, 379360930495, 215311288014, 223242348124⟩) 91625974997 174227471798)⟩)
              (.row ⟨114055813619, 117423580140, (.direct 30541785600 20803000397), (.chord (.midpoint ⟨472117486610, 120157192882, 159586450353, 404284049814, 202534479026, 271547962188⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop1H6NegPart0_checked : CutTop1H6NegPart0Tree.commonOK CutTop1H6NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
