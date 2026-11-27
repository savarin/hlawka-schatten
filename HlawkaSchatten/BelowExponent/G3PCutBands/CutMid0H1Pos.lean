/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H1Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H1PosBox : Box := ⟨![9/68, 1/20, 0, -8], ![9/34, 7/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid0H1PosTree : CertTree :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.row ⟨65259754744, 76698504229, (.direct 824633666698 805893367648), (.variance 207404018945)⟩)
        (.row ⟨65259754744, 76698504229, (.direct 30541785600 28251083232), (.variance 498751859057)⟩))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 2 (1/16)
              (.cut 1 (3/50)
                (.row ⟨65259754744, 71228276419, (.direct 30541785600 31739420148), (.chord .universal 0 3393555298)⟩)
                (.row ⟨71228276418, 76698504229, (.direct 30541785600 31947946764), (.chord .universal 0 3393555298)⟩))
              (.cut 1 (3/50)
                (.row ⟨65259754744, 71228276419, (.direct 30541785600 31739420148), (.chord .universal 3393555298 10180665226)⟩)
                (.row ⟨71228276418, 76698504229, (.direct 30541785600 31947946764), (.chord .universal 3393555298 10180665226)⟩)))
            (.cut 2 (5/16)
              (.cut 1 (3/50)
                (.row ⟨65259754744, 71228276419, (.direct 30541785600 31739420148), (.chord .universal 10180665226 43500686443)⟩)
                (.row ⟨71228276418, 76698504229, (.direct 30541785600 31947946764), (.chord .universal 10180665226 43500686443)⟩))
              (.row ⟨65259754744, 76698504229, (.direct 30541785600 31947946764), (.chord .universal 43500686443 91625974997)⟩)))
          (.row ⟨65259754744, 76698504229, (.direct 30541785600 31947946764), (.chord .universal 91625974997 274877906944)⟩))
        (.row ⟨65259754744, 76698504229, (.direct 174227225485 175112026720), (.variance 486621770630)⟩)))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cone)
            (.row ⟨65259754744, 76698504229, .zero, (.variance 309592422204)⟩))
          (.row ⟨65259754744, 76698504229, .zero, (.variance 309592422204)⟩))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.row ⟨65259754744, 76698504229, (.direct 391506126583 390315726274), (.variance 250764147958)⟩)
                (.row ⟨65259754744, 76698504229, (.direct 488587506629 486327555290), (.variance 236730856589)⟩))
              (.row ⟨65259754744, 76698504229, (.direct 593382169971 589914482085), (.variance 225058596267)⟩))
            (.row ⟨65259754744, 76698504229, (.direct 391506126583 390315726274), (.variance 250764147958)⟩))
          (.row ⟨65259754744, 76698504229, (.direct 391506126583 390315726274), (.variance 250764147958)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.row ⟨65259754744, 76698504229, (.direct 824633666698 818371107657), (.variance 206571251910)⟩)
                  (.row ⟨65259754744, 76698504229, (.direct 1082810704946 1073291492858), (.variance 192411852285)⟩))
                (.row ⟨65259754744, 76698504229, (.direct 1366046989981 1352849329194), (.variance 181095230867)⟩))
              (.row ⟨65259754744, 76698504229, (.direct 2002014560937 1980310192140), (.variance 163898184941)⟩))
            (.cut 3 (13/2)
              (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3480784758044), (.variance 141395042571)⟩)
              (.row ⟨65259754744, 76698504229, (.direct 5340438828596 5271888506630), (.variance 126830724538)⟩)))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.row ⟨65259754744, 76698504229, (.direct 824633666698 818371107657), (.variance 206571251910)⟩)
                (.row ⟨65259754744, 76698504229, (.direct 1366046989981 1352849329194), (.variance 181095230867)⟩))
              (.cut 3 (17/4)
                (.row ⟨65259754744, 76698504229, (.direct 2002014560937 1980310192140), (.variance 163898184941)⟩)
                (.row ⟨65259754744, 76698504229, (.direct 2723407729414 2691804296685), (.variance 151239800842)⟩)))
            (.cut 3 (13/2)
              (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3480784758044), (.variance 141395042571)⟩)
              (.row ⟨65259754744, 76698504229, (.direct 5340438828596 5271888506630), (.variance 126830724538)⟩))))
        (.row ⟨65259754744, 76698504229, (.direct 824633666698 818371107657), (.variance 206571251910)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid0H1Pos_checked : CutMid0H1PosTree.commonOK CutMid0H1PosBox true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
