/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid0H0Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid0H0PosBox : Box := ⟨![0, 1/20, 0, -8], ![9/68, 7/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid0H0PosTree : CertTree :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.row ⟨65259754744, 76698504229, (.direct 30541785600 29388299065), (.variance 493624180210)⟩)
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 2 (1/16)
              (.row ⟨65259754744, 76698504229, (.direct 30541785600 31242051228), (.chord .universal 0 3393555298)⟩)
              (.row ⟨65259754744, 76698504229, (.direct 30541785600 31242051228), (.chord .universal 3393555298 10180665226)⟩))
            (.cut 2 (5/16)
              (.row ⟨65259754744, 76698504229, (.direct 30541785600 31242051228), (.chord .universal 10180665226 43500686443)⟩)
              (.row ⟨65259754744, 76698504229, (.direct 30541785600 31242051228), (.chord .universal 43500686443 91625974997)⟩)))
          (.row ⟨65259754744, 76698504229, (.direct 30541785600 31242051228), (.chord .universal 91625974997 274877906944)⟩))
        (.row ⟨65259754744, 76698504229, (.direct 174227225485 174669542602), (.variance 488671898726)⟩)))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cone)
            (.row ⟨65259754744, 76698504229, .zero, (.variance 309737727641)⟩))
          (.row ⟨65259754744, 76698504229, .zero, (.variance 309737727641)⟩))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.row ⟨65259754744, 76698504229, (.direct 391506126583 390910973732), (.variance 250664103892)⟩)
                  (.row ⟨65259754744, 76698504229, (.direct 439055879922 438202270828), (.variance 243279185126)⟩))
                (.row ⟨65259754744, 76698504229, (.direct 488587506629 487457482889), (.variance 236587042111)⟩))
              (.row ⟨65259754744, 76698504229, (.direct 593382169971 591648095496), (.variance 224885727482)⟩))
            (.row ⟨65259754744, 76698504229, (.direct 391506126583 390910973732), (.variance 250664103892)⟩))
          (.row ⟨65259754744, 76698504229, (.direct 391506126583 390910973732), (.variance 250664103892)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.row ⟨65259754744, 76698504229, (.direct 824633666698 821501587173), (.variance 206364834634)⟩)
                  (.row ⟨65259754744, 76698504229, (.direct 1082810704946 1078049518771), (.variance 192189116211)⟩))
                (.row ⟨65259754744, 76698504229, (.direct 1366046989981 1359445638092), (.variance 180864722141)⟩))
              (.row ⟨65259754744, 76698504229, (.direct 2002014560937 1991157612074), (.variance 163663906659)⟩))
            (.cut 3 (13/2)
              (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3502159523186), (.variance 141168556117)⟩)
              (.row ⟨65259754744, 76698504229, (.direct 5340438828596 5306147314581), (.variance 126615784696)⟩)))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.row ⟨65259754744, 76698504229, (.direct 824633666698 821501587173), (.variance 206364834634)⟩)
                (.row ⟨65259754744, 76698504229, (.direct 1366046989981 1359445638092), (.variance 180864722141)⟩))
              (.cut 3 (17/4)
                (.row ⟨65259754744, 76698504229, (.direct 2002014560937 1991157612074), (.variance 163663906659)⟩)
                (.row ⟨65259754744, 76698504229, (.direct 2723407729414 2707598656727), (.variance 151008283788)⟩)))
            (.cut 3 (13/2)
              (.row ⟨65259754744, 76698504229, (.direct 3523554676644 3502159523186), (.variance 141168556117)⟩)
              (.row ⟨65259754744, 76698504229, (.direct 5340438828596 5306147314581), (.variance 126615784696)⟩))))
        (.row ⟨65259754744, 76698504229, (.direct 824633666698 821501587173), (.variance 206364834634)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid0H0Pos_checked : CutMid0H0PosTree.commonOK CutMid0H0PosBox true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
