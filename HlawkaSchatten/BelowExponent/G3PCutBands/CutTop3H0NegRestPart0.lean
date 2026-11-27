/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H0NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H0NegRestPart0Box : Box := (((⟨![0, 9/50, 0, -8], ![9/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop3H0NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3477141366137), (.variance 141433822931)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 811058807186), (.variance 207057316034)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 5272800635197), (.variance 126824979023)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3477141366137), (.variance 141433822931)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1973760134188), (.variance 164040436054)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 811058807186), (.variance 207057316034)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 5272800635197), (.variance 126824979023)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3477141366137), (.variance 141433822931)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1973760134188), (.variance 164040436054)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 811058807186), (.variance 207057316034)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 28877781181), (.variance 495894557339)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 324431497536), (.variance 263202877198)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨120689819474, 123862991200, (.direct 151782739331 147701560124), (.variance 323428064743)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨120689819474, 123862991200, (.direct 82716570280 79881465962), (.variance 379907836489)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 28877781181), (.variance 495894557339)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 54287234842 52044008550), (.chord (.midpoint ⟨416685621618, 156131741584, 223089189040, 318760928941, 223088797797, 168647478831⟩) 43500686443 91625974997)⟩))
                  (.cut 2 (13/32)
                    (.cut 0 (9/272)
                      (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 29705585964), (.chord (.midpoint ⟨466052171286, 123846815854, 204808430755, 338695745442, 204807924468, 244210969874⟩) 43500686443 65931360876)⟩))
                      (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 28877781181), (.chord (.midpoint ⟨454248823743, 131196882289, 205966500095, 337343478040, 209212597926, 240898130473⟩) 43500686443 65931360876)⟩)))
                    (.covered))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 324431497536), (.variance 263202877198)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨120689819474, 123862991200, (.direct 151782739331 147701560124), (.variance 323428064743)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨120689819474, 123862991200, (.direct 82716570280 79881465962), (.variance 379907836489)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop3H0NegRestPart0_ok : CutTop3H0NegRestPart0Tree.ok CutTop3H0NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
