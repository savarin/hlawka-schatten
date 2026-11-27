/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H1Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H1PosBox : Box := ⟨![9/136, 3/20, 0, -8], ![9/68, 4/25, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutTop0H1PosTree : CertTree :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.row ⟨110576703734, 114055813620, (.direct 824633666698 802187002831), (.variance 207654521677)⟩)
        (.row ⟨110576703734, 114055813620, (.direct 30541785600 27803637341), (.variance 500841293106)⟩))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.row ⟨110576703734, 114055813620, (.direct 30541785600 32230165216), (.chord .universal 0 10180665226)⟩)
            (.cut 2 (5/16)
              (.cut 2 (7/32)
                (.row ⟨110576703734, 114055813620, (.direct 30541785600 32230165216), (.chord .universal 10180665226 24716235638)⟩)
                (.row ⟨110576703734, 114055813620, (.direct 30541785600 32230165216), (.chord .universal 24716235638 43500686443)⟩))
              (.row ⟨110576703734, 114055813620, (.direct 30541785600 32230165216), (.chord .universal 43500686443 91625974997)⟩)))
          (.row ⟨110576703734, 114055813620, (.direct 30541785600 32230165216), (.chord .universal 91625974997 274877906944)⟩))
        (.row ⟨110576703734, 114055813620, (.direct 174227225485 175288035773), (.variance 485443860916)⟩)))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cone)
            (.row ⟨110576703734, 114055813620, .zero, (.variance 309508094644)⟩))
          (.row ⟨110576703734, 114055813620, .zero, (.variance 309508094644)⟩))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.row ⟨110576703734, 114055813620, (.direct 391506126583 390079199168), (.variance 250803954860)⟩)
                  (.row ⟨110576703734, 114055813620, (.direct 439055879922 437009476927), (.variance 243452886986)⟩))
                (.row ⟨110576703734, 114055813620, (.direct 488587506629 485878660392), (.variance 236788107931)⟩))
              (.row ⟨110576703734, 114055813620, (.direct 593382169971 589225865474), (.variance 225127440259)⟩))
            (.cut 3 (13/8)
              (.row ⟨110576703734, 114055813620, (.direct 391506126583 390079199168), (.variance 250803954860)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 593382169971 589225865474), (.variance 225127440259)⟩)))
          (.row ⟨110576703734, 114055813620, (.direct 391506126583 390079199168), (.variance 250803954860)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.row ⟨110576703734, 114055813620, (.direct 824633666698 817127919083), (.variance 206653501759)⟩)
                  (.row ⟨110576703734, 114055813620, (.direct 1082810704946 1071402262004), (.variance 192500638151)⟩))
                (.row ⟨110576703734, 114055813620, (.direct 1366046989981 1350230484415), (.variance 181187140324)⟩))
              (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1976004251578), (.variance 163991632358)⟩))
            (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3472301378325), (.variance 141485419262)⟩))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.row ⟨110576703734, 114055813620, (.direct 824633666698 817127919083), (.variance 206653501759)⟩)
                  (.row ⟨110576703734, 114055813620, (.direct 1082810704946 1071402262004), (.variance 192500638151)⟩))
                (.row ⟨110576703734, 114055813620, (.direct 1366046989981 1350230484415), (.variance 181187140324)⟩))
              (.cut 3 (17/4)
                (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1976004251578), (.variance 163991632358)⟩)
                (.row ⟨110576703734, 114055813620, (.direct 2723407729414 2685535270523), (.variance 151332169254)⟩)))
            (.cut 3 (13/2)
              (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3472301378325), (.variance 141485419262)⟩)
              (.row ⟨110576703734, 114055813620, (.direct 5340438828596 5258292859072), (.variance 126916512742)⟩))))
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.row ⟨110576703734, 114055813620, (.direct 824633666698 817127919083), (.variance 206653501759)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 2002014560937 1976004251578), (.variance 163991632358)⟩))
          (.cut 3 (13/2)
            (.row ⟨110576703734, 114055813620, (.direct 3523554676644 3472301378325), (.variance 141485419262)⟩)
            (.row ⟨110576703734, 114055813620, (.direct 5340438828596 5258292859072), (.variance 126916512742)⟩)))))

set_option maxRecDepth 16000 in
theorem CutTop0H1Pos_checked : CutTop0H1PosTree.commonOK CutTop0H1PosBox true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
