/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H1NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H1NegRestPart0Box : Box := (((⟨![9/136, 4/25, 0, -8], ![9/68, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop1H1NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3441540704828), (.variance 141815476288)⟩))
          (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 800661924032), (.variance 207758021928)⟩)))
        (.cut 3 (-5)
          (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3441540704828), (.variance 141815476288)⟩))
          (.cut 3 (-7/2)
            (.original (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1952098327244), (.variance 164515153279)⟩))
            (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 800661924032), (.variance 207758021928)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨114055813619, 117423580140, (.direct 5340438828596 5220904462548), (.variance 127153883154)⟩))
          (.original (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3441540704828), (.variance 141815476288)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1952098327244), (.variance 164515153279)⟩))
          (.original (.row ⟨114055813619, 117423580140, (.direct 824633666698 800661924032), (.variance 207758021928)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨114055813619, 117423580140, (.direct 30541785600 27620070543), (.variance 501710804855)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨114055813619, 117423580140, (.direct 331294831298 319183371582), (.variance 264329291294)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨114055813619, 117423580140, (.direct 151782739331 144587238228), (.variance 325237971771)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨114055813619, 117423580140, (.direct 82716570280 77723400776), (.variance 382642204963)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨114055813619, 117423580140, (.direct 30541785600 27620070543), (.variance 501710804855)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨114055813619, 117423580140, (.direct 54287234842 50340622925), (.variance 428734353558)⟩))
                  (.cut 2 (13/32)
                    (.original (.row ⟨114055813619, 117423580140, (.direct 30541785600 27620070543), (.chord (.midpoint ⟨445557885148, 136754491255, 205983778445, 337323400692, 212440739976, 230973808939⟩) 43500686443 65931360876)⟩))
                    (.covered))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨114055813619, 117423580140, (.direct 331294831298 319183371582), (.variance 264329291294)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨114055813619, 117423580140, (.direct 151782739331 144587238228), (.variance 325237971771)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨114055813619, 117423580140, (.direct 82716570280 77723400776), (.variance 382642204963)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop1H1NegRestPart0_ok : CutTop1H1NegRestPart0Tree.ok CutTop1H1NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
