/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H0NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H0NegPart0Box : Box := (((⟨![0, 4/25, 0, -8], ![9/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop1H0NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3482472457306), (.variance 141377096011)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 812616568006), (.variance 206953306018)⟩))
        (.cut 3 (-5)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3482472457306), (.variance 141377096011)⟩)
          (.cut 3 (-7/2)
            (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1977004434522), (.variance 163969903516)⟩)
            (.row ⟨114055813619, 117423580140, (.direct 824633666698 812616568006), (.variance 206953306018)⟩))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.row ⟨114055813619, 117423580140, (.direct 5340438828596 5280571272230), (.variance 126776082441)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 3523554676644 3482472457306), (.variance 141377096011)⟩))
        (.cut 3 (-7/2)
          (.row ⟨114055813619, 117423580140, (.direct 2002014560937 1977004434522), (.variance 163969903516)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 824633666698 812616568006), (.variance 206953306018)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨114055813619, 117423580140, (.direct 30541785600 29067480028), (.variance 495045056380)⟩)
        (.cut 3 (-9/8)
          (.row ⟨114055813619, 117423580140, (.direct 331294831298 325218387864), (.variance 263035968133)⟩)
          (.cut 3 (-11/16)
            (.row ⟨114055813619, 117423580140, (.direct 151782739331 148169006084), (.variance 323160563061)⟩)
            (.cut 2 (5/16)
              (.cut 3 (-15/32)
                (.row ⟨114055813619, 117423580140, (.direct 82716570280 80205796485), (.variance 379504954384)⟩)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 29067480028), (.variance 495045056380)⟩))
              (.cut 3 (-15/32)
                (.row ⟨114055813619, 117423580140, (.direct 82716570280 80205796485), (.variance 379504954384)⟩)
                (.cut 3 (-23/64)
                  (.row ⟨114055813619, 117423580140, (.direct 54287234842 52300323218), (.variance 424468177464)⟩)
                  (.cut 2 (13/32)
                    (.row ⟨114055813619, 117423580140, (.direct 30541785600 29067480028), (.chord (.midpoint ⟨470415754001, 121186453226, 203173575985, 340627158046, 203173060060, 238375158869⟩) 43500686443 65931360876)⟩)
                    (.row ⟨114055813619, 117423580140, (.direct 30541785600 29067480028), (.chord (.midpoint ⟨531196898587, 87202123942, 179935678507, 371283767912, 179935037987, 282711267771⟩) 65931360876 91625974997)⟩))))))))
      (.cut 3 (-9/8)
        (.row ⟨114055813619, 117423580140, (.direct 331294831298 325218387864), (.variance 263035968133)⟩)
        (.cut 3 (-11/16)
          (.row ⟨114055813619, 117423580140, (.direct 151782739331 148169006084), (.variance 323160563061)⟩)
          (.cut 3 (-15/32)
            (.row ⟨114055813619, 117423580140, (.direct 82716570280 80205796485), (.variance 379504954384)⟩)
            (.cut 3 (-23/64)
              (.row ⟨114055813619, 117423580140, (.direct 54287234842 52300323218), (.variance 424468177464)⟩)
              (.cut 2 (3/4)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 29067480028), (.chord (.midpoint ⟨623708285793, 45859379264, 141941868952, 439329590159, 141941080853, 308055631295⟩) 91625974997 174227471798)⟩)
                (.row ⟨114055813619, 117423580140, (.direct 30541785600 29067480028), (.chord (.midpoint ⟨671990548255, 29067277543, 119957126879, 495045056380, 119956291258, 342254087946⟩) 174227471798 274877906944)⟩)))))))

set_option maxRecDepth 16000 in
theorem CutTop1H0NegPart0_checked : CutTop1H0NegPart0Tree.commonOK CutTop1H0NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
