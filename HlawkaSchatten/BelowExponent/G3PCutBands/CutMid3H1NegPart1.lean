/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H1NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H1NegPart1Box : Box := (((((((⟨![9/68, 11/100, 0, -8], ![9/34, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).lowerChild 3 (0)

set_option maxRecDepth 16000 in
def CutMid3H1NegPart1Tree : CertTree :=
  .cut 1 (3/25)
    (.cut 3 (-1/8)
      (.row ⟨95281442640, 99345187400, (.direct 10180561190 7838508693), (.variance 697731576495)⟩)
      (.cut 1 (23/200)
        (.cut 0 (27/136)
          (.cut 1 (9/80)
            (.row ⟨95281442640, 96314804182, (.direct 0 242694866), (.chord .universal 0 10180665226)⟩)
            (.row ⟨96314804181, 97336292160, (.direct 0 251826757), (.chord .universal 0 10180665226)⟩))
          (.cut 1 (9/80)
            (.cut 3 (-1/16)
              (.row ⟨95281442640, 96314804182, (.direct 3393509060 2068763180), (.chord .universal 0 10180665226)⟩)
              (.row ⟨95281442640, 96314804182, (.direct 0 382898609), (.chord .universal 0 10180665226)⟩))
            (.row ⟨96314804181, 97336292160, (.direct 0 397305953), (.chord .universal 0 10180665226)⟩)))
        (.cut 0 (27/136)
          (.row ⟨97336292159, 99345187400, (.direct 0 270536357), (.chord .universal 0 10180665226)⟩)
          (.cut 1 (47/400)
            (.row ⟨97336292159, 98346296770, (.direct 0 411947799), (.chord .universal 0 10180665226)⟩)
            (.row ⟨98346296769, 99345187400, (.direct 0 426824007), (.chord .universal 0 10180665226)⟩)))))
    (.cut 3 (-1/8)
      (.row ⟨99345187399, 103236350716, (.direct 10180561190 7640863183), (.variance 702413205770)⟩)
      (.cut 1 (1/8)
        (.cut 0 (27/136)
          (.row ⟨99345187399, 101311009181, (.direct 0 289839918), (.chord .universal 0 10180665226)⟩)
          (.cut 3 (-1/16)
            (.row ⟨99345187399, 101311009181, (.direct 3393509060 1928151468), (.chord .universal 0 10180665226)⟩)
            (.row ⟨99345187399, 101311009181, (.direct 0 457279149), (.chord .universal 0 10180665226)⟩)))
        (.cut 0 (27/136)
          (.row ⟨101311009180, 103236350716, (.direct 0 309737242), (.chord .universal 0 10180665226)⟩)
          (.row ⟨101311009180, 103236350716, (.direct 0 488671068), (.chord .universal 0 10180665226)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid3H1NegPart1_checked : CutMid3H1NegPart1Tree.commonOK CutMid3H1NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
