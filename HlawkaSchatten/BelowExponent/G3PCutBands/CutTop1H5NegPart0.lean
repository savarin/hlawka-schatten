/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H5NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H5NegPart0Box : Box := (((⟨![45/136, 4/25, 0, -8], ![27/68, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop1H5NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3279608197477), (.variance 143616558381)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 753501111791), (.variance 211087102882)⟩))
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3279608197477), (.variance 143616558381)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 753501111791), (.variance 211087102882)⟩)))
      (.cut 3 (-5)
        (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3279608197477), (.variance 143616558381)⟩)
        (.cut 3 (-7/2)
          (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1853645146212), (.variance 166759712013)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 753501111791), (.variance 211087102882)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 22109043931), (.variance 531818505362)⟩)
        (.cut 3 (-9/8)
          (.row ⟨114055813619, 117423580140, (.direct 331294831298 295463641132), (.variance 269728563170)⟩)
          (.cut 3 (-11/16)
            (.row ⟨114055813619, 117423580140, (.direct 151782739331 130586831761), (.variance 334028439398)⟩)
            (.cut 3 (-15/32)
              (.row ⟨114055813619, 117423580140, (.direct 82716570280 68085526352), (.variance 396140285045)⟩)
              (.cut 2 (5/16)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 22109043931), (.variance 531818505362)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨114055813619, 117423580140, (.direct 54287234842 42782339959), (.chord (.midpoint ⟨297269107895, 253140581520, 238390722582, 304104936452, 266646046270, 118751901491⟩) 43500686443 91625974997)⟩)
                  (.row ⟨114055813619, 117423580140, (.direct 30541785600 22109043931), (.chord (.midpoint ⟨397146267717, 170073796035, 198504554004, 346292457157, 230243507165, 199489388723⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨114055813619, 117423580140, (.direct 331294831298 295463641132), (.variance 269728563170)⟩)
        (.cut 3 (-11/16)
          (.row ⟨114055813619, 117423580140, (.direct 151782739331 130586831761), (.variance 334028439398)⟩)
          (.cut 3 (-15/32)
            (.row ⟨114055813619, 117423580140, (.direct 82716570280 68085526352), (.variance 396140285045)⟩)
            (.cut 2 (3/4)
              (.row ⟨114055813619, 117423580140, (.direct 30541785600 22109043931), (.chord (.midpoint ⟨467088694214, 123212113730, 169437217621, 387462991882, 204419911107, 232295726736⟩) 91625974997 174227471798)⟩)
              (.row ⟨114055813619, 117423580140, (.direct 30541785600 22109043931), (.chord (.midpoint ⟨503607729458, 101929743263, 153495910006, 415601197588, 190602761210, 280352432851⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop1H5NegPart0_checked : CutTop1H5NegPart0Tree.commonOK CutTop1H5NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
