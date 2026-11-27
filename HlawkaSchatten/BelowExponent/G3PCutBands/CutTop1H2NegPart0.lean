/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H2NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H2NegPart0Box : Box := (((⟨![9/68, 4/25, 0, -8], ![27/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop1H2NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3400787840718), (.variance 142258526010)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 788772797506), (.variance 208573507124)⟩))
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3400787840718), (.variance 142258526010)⟩)
          (.cut 3 (-7/2)
            (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1927308951202), (.variance 165066634734)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 824633666698 788772797506), (.variance 208573507124)⟩))))
      (.cut 3 (-5)
        (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3400787840718), (.variance 142258526010)⟩)
        (.cut 3 (-7/2)
          (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1927308951202), (.variance 165066634734)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 788772797506), (.variance 208573507124)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 26200130262), (.variance 508692839901)⟩)
        (.cut 3 (-9/8)
          (.row ⟨114055813619, 117423580140, (.direct 331294831298 313190178856), (.variance 265644555737)⟩)
          (.cut 3 (-11/16)
            (.row ⟨114055813619, 117423580140, (.direct 151782739331 141037922542), (.variance 327361628234)⟩)
            (.cut 3 (-15/32)
              (.row ⟨114055813619, 117423580140, (.direct 82716570280 75269928307), (.variance 385869676578)⟩)
              (.cut 2 (5/16)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 26200130262), (.variance 508692839901)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨114055813619, 117423580140, (.direct 54287234842 48408683259), (.variance 433150350551)⟩)
                  (.row ⟨114055813619, 117423580140, (.direct 30541785600 26200130262), (.chord (.midpoint ⟨475857897288, 117911046688, 187519580000, 360566099357, 201128825604, 223400201592⟩) 43500686443 91625974997)⟩)))))))
      (.cut 3 (-9/8)
        (.row ⟨114055813619, 117423580140, (.direct 331294831298 313190178856), (.variance 265644555737)⟩)
        (.cut 3 (-11/16)
          (.row ⟨114055813619, 117423580140, (.direct 151782739331 141037922542), (.variance 327361628234)⟩)
          (.cut 3 (-15/32)
            (.row ⟨114055813619, 117423580140, (.direct 82716570280 75269928307), (.variance 385869676578)⟩)
            (.cut 2 (3/4)
              (.cut 3 (-23/64)
                (.row ⟨114055813619, 117423580140, (.direct 54287234842 48408683259), (.chord (.midpoint ⟨480215299027, 115322278627, 185794113983, 362938756338, 199487638749, 258074588902⟩) 91625974997 174227471798)⟩)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 26200130262), (.chord (.midpoint ⟨559063747047, 73464196586, 153359111887, 415864194448, 168903180106, 292798141079⟩) 91625974997 174227471798)⟩))
              (.row ⟨114055813619, 117423580140, (.direct 30541785600 26200130262), (.chord (.midpoint ⟨602496040315, 54269198236, 134086244419, 457439902824, 151041606499, 305666603250⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop1H2NegPart0_checked : CutTop1H2NegPart0Tree.commonOK CutTop1H2NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
