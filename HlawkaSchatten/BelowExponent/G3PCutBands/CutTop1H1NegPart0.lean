/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H1NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H1NegPart0Box : Box := (((⟨![9/136, 4/25, 0, -8], ![9/68, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop1H1NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3441540704828), (.variance 141815476288)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 800661924032), (.variance 207758021928)⟩))
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3441540704828), (.variance 141815476288)⟩)
          (.cut 3 (-7/2)
            (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1952098327244), (.variance 164515153279)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 824633666698 800661924032), (.variance 207758021928)⟩))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.row ⟨114055813619, 117423580140, (.direct 5340438828596 5220904462548), (.variance 127153883154)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3441540704828), (.variance 141815476288)⟩))
        (.cut 3 (-7/2)
          (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1952098327244), (.variance 164515153279)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 800661924032), (.variance 207758021928)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 27620070543), (.variance 501710804855)⟩)
        (.cut 3 (-9/8)
          (.row ⟨114055813619, 117423580140, (.direct 331294831298 319183371582), (.variance 264329291294)⟩)
          (.cut 3 (-11/16)
            (.row ⟨114055813619, 117423580140, (.direct 151782739331 144587238228), (.variance 325237971771)⟩)
            (.cut 3 (-15/32)
              (.row ⟨114055813619, 117423580140, (.direct 82716570280 77723400776), (.variance 382642204963)⟩)
              (.cut 2 (5/16)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 27620070543), (.variance 501710804855)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨114055813619, 117423580140, (.direct 54287234842 50340622925), (.variance 428734353558)⟩)
                  (.cut 2 (13/32)
                    (.row ⟨114055813619, 117423580140, (.direct 30541785600 27620070543), (.chord (.midpoint ⟨445557885148, 136754491255, 205983778445, 337323400692, 212440739976, 230973808939⟩) 43500686443 65931360876)⟩)
                    (.row ⟨114055813619, 117423580140, (.direct 30541785600 27620070543), (.chord (.midpoint ⟨503246614832, 102130098576, 183755392029, 365791177510, 190740949525, 275245472408⟩) 65931360876 91625974997)⟩))))))))
      (.cut 3 (-9/8)
        (.row ⟨114055813619, 117423580140, (.direct 331294831298 319183371582), (.variance 264329291294)⟩)
        (.cut 3 (-11/16)
          (.row ⟨114055813619, 117423580140, (.direct 151782739331 144587238228), (.variance 325237971771)⟩)
          (.cut 3 (-15/32)
            (.row ⟨114055813619, 117423580140, (.direct 82716570280 77723400776), (.variance 382642204963)⟩)
            (.cut 2 (3/4)
              (.cut 3 (-23/64)
                (.row ⟨114055813619, 117423580140, (.direct 54287234842 50340622925), (.chord (.midpoint ⟨510005915795, 98412653031, 181092585239, 369599283392, 188148534891, 266268003398⟩) 91625974997 174227471798)⟩)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 27620070543), (.chord (.midpoint ⟨591059788793, 59064896205, 147728778509, 427048474304, 155836651834, 300495604171⟩) 91625974997 174227471798)⟩))
              (.row ⟨114055813619, 117423580140, (.direct 30541785600 27620070543), (.chord (.midpoint ⟨636893411667, 40949130211, 127161031720, 474978801957, 136130628824, 313778533838⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop1H1NegPart0_checked : CutTop1H1NegPart0Tree.commonOK CutTop1H1NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
