/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H1NegPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H1NegPart0Box : Box := (((⟨![9/136, 3/20, 0, -8], ![9/68, 4/25, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop0H1NegPart0Tree : CertTree :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3446764980694), (.variance 141759158819)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 802187002831), (.variance 207654521677)⟩))
        (.cut 3 (-5)
          (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3446764980694), (.variance 141759158819)⟩)
          (.cut 3 (-7/2)
            (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1955276750397), (.variance 164445083283)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 824633666698 802187002831), (.variance 207654521677)⟩))))
      (.cut 3 (-5)
        (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3446764980694), (.variance 141759158819)⟩)
        (.cut 3 (-7/2)
          (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1955276750397), (.variance 164445083283)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 824633666698 802187002831), (.variance 207654521677)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.row ⟨110576703734, 114055813620, (.direct 30541785600 27803637341), (.variance 500841293106)⟩)
        (.cut 3 (-9/8)
          (.row ⟨110576703734, 114055813620, (.direct 331294831298 319952784940), (.variance 264162694393)⟩)
          (.cut 3 (-11/16)
            (.row ⟨110576703734, 114055813620, (.direct 151782739331 145043459590), (.variance 324969775971)⟩)
            (.cut 3 (-15/32)
              (.row ⟨110576703734, 114055813620, (.direct 82716570280 78039234893), (.variance 382236082406)⟩)
              (.cut 0 (27/272)
                (.cut 3 (-23/64)
                  (.row ⟨110576703734, 114055813620, (.direct 54287234842 51505099371), (.variance 426174625118)⟩)
                  (.cut 2 (5/16)
                    (.row ⟨110576703734, 114055813620, (.direct 30541785600 28479309771), (.variance 497702127498)⟩)
                    (.row ⟨110576703734, 114055813620, (.direct 30541785600 28479309771), (.chord (.midpoint ⟨498267885677, 104912674611, 185707705866, 363058564967, 192642703954, 236636563107⟩) 43500686443 91625974997)⟩)))
                (.cut 2 (5/16)
                  (.row ⟨110576703734, 114055813620, (.direct 30541785600 27803637341), (.variance 500841293106)⟩)
                  (.cut 3 (-23/64)
                    (.row ⟨110576703734, 114055813620, (.direct 54287234842 50589681873), (.variance 428180636889)⟩)
                    (.row ⟨110576703734, 114055813620, (.direct 30541785600 27803637341), (.chord (.midpoint ⟨484289832790, 112928548597, 187686165330, 360339005771, 197949285521, 232784204608⟩) 43500686443 91625974997)⟩))))))))
      (.cut 3 (-9/8)
        (.row ⟨110576703734, 114055813620, (.direct 331294831298 319952784940), (.variance 264162694393)⟩)
        (.cut 3 (-11/16)
          (.row ⟨110576703734, 114055813620, (.direct 151782739331 145043459590), (.variance 324969775971)⟩)
          (.cut 3 (-15/32)
            (.row ⟨110576703734, 114055813620, (.direct 82716570280 78039234893), (.variance 382236082406)⟩)
            (.cut 2 (3/4)
              (.cut 3 (-23/64)
                (.row ⟨110576703734, 114055813620, (.direct 54287234842 50589681873), (.chord (.midpoint ⟨509226297019, 98837898413, 181400457077, 369154109885, 188448181786, 266080111543⟩) 91625974997 174227471798)⟩)
                (.row ⟨110576703734, 114055813620, (.direct 30541785600 27803637341), (.chord (.midpoint ⟨590302756740, 59388841759, 148055823639, 426378962413, 156151552556, 300336014028⟩) 91625974997 174227471798)⟩))
              (.row ⟨110576703734, 114055813620, (.direct 30541785600 27803637341), (.chord (.midpoint ⟨636309730423, 41161354665, 127433851919, 474257095541, 136390590459, 313667061257⟩) 174227471798 274877906944)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop0H1NegPart0_checked : CutTop0H1NegPart0Tree.commonOK CutTop0H1NegPart0Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
