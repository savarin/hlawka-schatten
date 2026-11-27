/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0NegRestPart1Box : Box := (((((((⟨![0, 9/100, 0, -8], ![9/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).lowerChild 3 (0)

set_option maxRecDepth 16000 in
def CutMid2H0NegRestPart1Tree : RatioRemainder :=
  .cut 1 (1/10)
    (.cut 1 (19/200)
      (.cut 3 (-1/8)
        (.original (.row ⟨86531900008, 88806993133, (.direct 10180561190 9238941357), (.variance 668335523310)⟩))
        (.cut 0 (9/136)
          (.cut 1 (37/400)
            (.original (.row ⟨86531900008, 87677441236, (.direct 0 30679419), (.chord .universal 0 10180665226)⟩))
            (.original (.row ⟨87677441235, 88806993133, (.direct 0 32070572), (.chord .universal 0 10180665226)⟩)))
          (.cut 1 (37/400)
            (.original (.row ⟨86531900008, 87677441236, (.direct 0 92038251), (.chord .universal 0 10180665226)⟩))
            (.original (.row ⟨87677441235, 88806993133, (.direct 0 96211709), (.chord .universal 0 10180665226)⟩)))))
      (.cut 3 (-1/8)
        (.original (.row ⟨88806993132, 91020629598, (.direct 10180561190 9187759033), (.variance 669308455297)⟩))
        (.cut 0 (9/136)
          (.original (.row ⟨88806993132, 91020629598, (.direct 0 34931964), (.chord .universal 0 10180665226)⟩))
          (.cut 1 (39/400)
            (.original (.row ⟨88806993132, 89921191063, (.direct 0 100464317), (.chord .universal 0 10180665226)⟩))
            (.original (.row ⟨89921191062, 91020629598, (.direct 0 104795883), (.chord .universal 0 10180665226)⟩))))))
    (.cut 1 (21/200)
      (.cut 3 (-1/8)
        (.original (.row ⟨91020629597, 93177423805, (.direct 10180561190 9136412464), (.variance 670291405919)⟩))
        (.cut 0 (9/136)
          (.original (.row ⟨91020629597, 93177423805, (.direct 0 37898415), (.chord .universal 0 10180665226)⟩))
          (.cut 1 (41/400)
            (.original (.row ⟨91020629597, 92105866080, (.direct 0 109206239), (.chord .universal 0 10180665226)⟩))
            (.original (.row ⟨92105866079, 93177423805, (.direct 0 113695238), (.chord .universal 0 10180665226)⟩)))))
      (.cut 3 (-1/8)
        (.original (.row ⟨93177423804, 95281442641, (.direct 10180561190 9084901347), (.variance 671284535891)⟩))
        (.cut 0 (9/136)
          (.original (.row ⟨93177423804, 95281442641, (.direct 0 40969556), (.chord .universal 0 10180665226)⟩))
          (.original (.row ⟨93177423804, 95281442641, (.direct 0 122908660), (.chord .universal 0 10180665226)⟩)))))

set_option maxRecDepth 16000 in
theorem CutMid2H0NegRestPart1_ok : CutMid2H0NegRestPart1Tree.geometryOK CutMid2H0NegPowerCache CutMid2H0NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
