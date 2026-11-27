/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H7NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H7NegPart0Box : Box := (((⟨![63/136, 4/25, 0, -8], ![9/17, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop1H7NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3199726618693), (.variance 144546889585)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 730319050953), (.variance 212821457326)⟩))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.row ⟨114055813619, 117423580140, (.direct 5340438828596 4868193134741), (.variance 129504322789)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3199726618693), (.variance 144546889585)⟩))
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 730319050953), (.variance 212821457326)⟩)))
      (.cut 3 (-5)
        (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3199726618693), (.variance 144546889585)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 824633666698 730319050953), (.variance 212821457326)⟩)))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 19526543152), (.variance 549400885193)⟩)
        (.cut 3 (-9/8)
          (.row ⟨114055813619, 117423580140, (.direct 331294831298 283858979914), (.variance 272573478302)⟩)
          (.cut 3 (-11/16)
            (.row ⟨114055813619, 117423580140, (.direct 151782739331 123785715315), (.variance 338739734420)⟩)
            (.cut 3 (-15/32)
              (.row ⟨114055813619, 117423580140, (.direct 82716570280 63445212563), (.variance 403530682595)⟩)
              (.cut 2 (5/16)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 19526543152), (.variance 549400885193)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨114055813619, 117423580140, (.direct 54287234842 39175778182), (.chord (.midpoint ⟨254144321746, 296205515984, 244166943855, 298982873242, 282564360444, 94066257145⟩) 43500686443 91625974997)⟩)
                  (.row ⟨114055813619, 117423580140, (.direct 30541785600 19526543152), (.chord (.midpoint ⟨347644060771, 208621014423, 205593806135, 337777248380, 248274269926, 182351889336⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨114055813619, 117423580140, (.direct 331294831298 283858979914), (.variance 272573478302)⟩)
        (.cut 3 (-11/16)
          (.row ⟨114055813619, 117423580140, (.direct 151782739331 123785715315), (.variance 338739734420)⟩)
          (.cut 3 (-15/32)
            (.row ⟨114055813619, 117423580140, (.direct 82716570280 63445212563), (.variance 403530682595)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 30541785600 19526543152), (.chord (.midpoint ⟨441384093274, 139468072333, 165516332358, 393953089440, 213986892561, 213920578909⟩) 91625974997 274877906944)⟩)))))

set_option maxRecDepth 16000 in
theorem CutTop1H7NegPart0_checked : CutTop1H7NegPart0Tree.commonOK CutTop1H7NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
