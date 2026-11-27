/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H5PosRest`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H5PosRestBox : Box := ⟨![45/136, 9/50, 0, -8], ![27/68, 19/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop3H5PosRestTree : RatioRemainder :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (-5)
              (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3248368708090), (.chord .universal 0 10180665226)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 744428541967), (.variance 211757738889)⟩)))
            (.cut 3 (-5)
              (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3248368708090), (.variance 143976945665)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 744428541967), (.variance 211757738889)⟩))))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 744428541967), (.variance 211757738889)⟩)))
        (.cut 2 (1/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 21087833510), (.variance 538445208770)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 21087833510), (.chord .universal 91625974997 274877906944)⟩))))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (0)
              (.original (.row ⟨120689819474, 123862991200, (.direct 0 1785585184), (.chord .universal 0 10180665226)⟩))
              (.cut 3 (1/8)
                (.original (.row ⟨120689819474, 123862991200, (.direct 10180561190 15275518371), (.chord .universal 0 10180665226)⟩))
                (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 36812648456), (.variance 598105938904)⟩))))
            (.cut 2 (5/16)
              (.cut 3 (0)
                (.cut 1 (37/200)
                  (.original (.row ⟨120689819474, 122287555846, (.direct 0 1704216908), (.chord .universal 10180665226 43500686443)⟩))
                  (.original (.row ⟨122287555845, 123862991200, (.direct 0 1785585184), (.chord .universal 10180665226 43500686443)⟩)))
                (.cut 3 (1/8)
                  (.cut 2 (7/32)
                    (.cut 3 (1/16)
                      (.covered)
                      (.original (.row ⟨120689819474, 123862991200, (.direct 10180561190 15275518371), (.chord (.midpoint ⟨388113984353, 176754239997, 202162521399, 341834965771, 233540856215, 138857072873⟩) 10180665226 24716235638)⟩)))
                    (.covered))
                  (.cut 2 (7/32)
                    (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 36812648456), (.variance 598105938904)⟩))
                    (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 36812648456), (.chord (.midpoint ⟨356126223963, 201670552263, 215005491871, 327218481215, 245188788613, 140417227414⟩) 24716235638 43500686443)⟩)))))
              (.covered)))
          (.covered))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (1/2)
              (.original (.row ⟨120689819474, 123862991200, (.direct 91625662891 97752300374), (.variance 470042713886)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 174227225485 178079611834), (.variance 361638361544)⟩)))
            (.cut 3 (1/2)
              (.cut 3 (3/8)
                (.original (.row ⟨120689819474, 123862991200, (.direct 58075547817 64598826840), (.variance 470042713886)⟩))
                (.original (.row ⟨120689819474, 123862991200, (.direct 91625662891 97752300374), (.variance 403980737797)⟩)))
              (.original (.row ⟨120689819474, 123862991200, (.direct 174227225485 178079611834), (.variance 361638361544)⟩))))
          (.cut 3 (1/2)
            (.cut 3 (3/8)
              (.covered)
              (.original (.row ⟨120689819474, 123862991200, (.direct 91625662891 97752300374), (.variance 403980737797)⟩)))
            (.original (.row ⟨120689819474, 123862991200, (.direct 174227225485 178079611834), (.variance 361638361544)⟩))))))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.original (.cone))
            (.original (.row ⟨120689819474, 123862991200, .zero, (.variance 308346175074)⟩)))
          (.original (.row ⟨120689819474, 123862991200, .zero, (.variance 308346175074)⟩)))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 386346459376), (.variance 251436227505)⟩))
                  (.original (.row ⟨120689819474, 123862991200, (.direct 439055879922 431659845757), (.variance 244239357240)⟩)))
                (.original (.row ⟨120689819474, 123862991200, (.direct 488587506629 478801451126), (.variance 237699642108)⟩)))
              (.original (.row ⟨120689819474, 123862991200, (.direct 593382169971 578377524472), (.variance 226225580881)⟩)))
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 386346459376), (.variance 251436227505)⟩))
                (.original (.row ⟨120689819474, 123862991200, (.direct 488587506629 478801451126), (.variance 237699642108)⟩)))
              (.original (.row ⟨120689819474, 123862991200, (.direct 593382169971 578377524472), (.variance 226225580881)⟩))))
          (.original (.row ⟨120689819474, 123862991200, (.direct 391506126583 386346459376), (.variance 251436227505)⟩))))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 797564515406), (.variance 207968996898)⟩))
                  (.original (.row ⟨120689819474, 123862991200, (.direct 1082810704946 1041694917678), (.variance 193923284650)⟩)))
                (.original (.row ⟨120689819474, 123862991200, (.direct 1366046989981 1309072990291), (.variance 182661815741)⟩)))
              (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1908383327056), (.variance 165493727774)⟩)))
            (.cut 3 (13/2)
              (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3339187876970), (.variance 142941091473)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 5045057702156), (.variance 128299787614)⟩))))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 797564515406), (.variance 207968996898)⟩))
                  (.original (.row ⟨120689819474, 123862991200, (.direct 1082810704946 1041694917678), (.variance 193923284650)⟩)))
                (.original (.row ⟨120689819474, 123862991200, (.direct 1366046989981 1309072990291), (.variance 182661815741)⟩)))
              (.cut 3 (17/4)
                (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1908383327056), (.variance 165493727774)⟩))
                (.original (.row ⟨120689819474, 123862991200, (.direct 2723407729414 2587133794100), (.variance 152818683554)⟩))))
            (.cut 3 (13/2)
              (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3339187876970), (.variance 142941091473)⟩))
              (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 5045057702156), (.variance 128299787614)⟩)))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 797564515406), (.variance 207968996898)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1908383327056), (.variance 165493727774)⟩)))
          (.cut 3 (13/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3339187876970), (.variance 142941091473)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 5045057702156), (.variance 128299787614)⟩))))))

set_option maxRecDepth 16000 in
theorem CutTop3H5PosRest_ok : CutTop3H5PosRestTree.ok CutTop3H5PosRestBox true (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
