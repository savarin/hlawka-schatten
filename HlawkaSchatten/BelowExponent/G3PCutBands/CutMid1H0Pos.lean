/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid1H0Pos`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid1H0PosBox : Box := ⟨![0, 7/100, 0, -8], ![9/68, 9/100, 1, 8]⟩

set_option maxRecDepth 16000 in
def CutMid1H0PosTree : CertTree :=
  .cut 3 (3/4)
    (.cut 3 (-1/4)
      (.cut 3 (-2)
        (.row ⟨76698504228, 86531900009, (.direct 824633666698 812443059617), (.variance 206964878531)⟩)
        (.row ⟨76698504228, 86531900009, (.direct 30541785600 29046334734), (.variance 495139401389)⟩))
      (.cut 3 (1/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 2 (1/16)
              (.row ⟨76698504228, 86531900009, (.direct 30541785600 31452628657), (.chord .universal 0 3393555298)⟩)
              (.row ⟨76698504228, 86531900009, (.direct 30541785600 31452628657), (.chord .universal 3393555298 10180665226)⟩))
            (.cut 2 (5/16)
              (.row ⟨76698504228, 86531900009, (.direct 30541785600 31452628657), (.chord .universal 10180665226 43500686443)⟩)
              (.row ⟨76698504228, 86531900009, (.direct 30541785600 31452628657), (.chord .universal 43500686443 91625974997)⟩)))
          (.row ⟨76698504228, 86531900009, (.direct 30541785600 31452628657), (.chord .universal 91625974997 274877906944)⟩))
        (.row ⟨76698504228, 86531900009, (.direct 174227225485 174801880471), (.variance 488671898726)⟩)))
    (.cut 3 (2)
      (.cut 3 (5/4)
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cone)
            (.row ⟨76698504228, 86531900009, .zero, (.variance 309737727641)⟩))
          (.row ⟨76698504228, 86531900009, .zero, (.variance 309737727641)⟩))
        (.cut 2 (1/2)
          (.cut 2 (1/8)
            (.cut 3 (13/8)
              (.cut 3 (23/16)
                (.cut 3 (43/32)
                  (.row ⟨76698504228, 86531900009, (.direct 391506126583 390732854131), (.variance 250694020535)⟩)
                  (.row ⟨76698504228, 86531900009, (.direct 439055879922 437946819015), (.variance 243316335319)⟩))
                (.row ⟨76698504228, 86531900009, (.direct 488587506629 487119332789), (.variance 236630036903)⟩))
              (.row ⟨76698504228, 86531900009, (.direct 593382169971 591129240960), (.variance 224937398427)⟩))
            (.row ⟨76698504228, 86531900009, (.direct 391506126583 390732854131), (.variance 250694020535)⟩))
          (.row ⟨76698504228, 86531900009, (.direct 391506126583 390732854131), (.variance 250694020535)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.cut 3 (19/8)
                  (.row ⟨76698504228, 86531900009, (.direct 824633666698 820564556467), (.variance 206426516256)⟩)
                  (.row ⟨76698504228, 86531900009, (.direct 1082810704946 1076625211351), (.variance 192255661608)⟩))
                (.row ⟨76698504228, 86531900009, (.direct 1366046989981 1357470931153), (.variance 180933580224)⟩))
              (.cut 3 (17/4)
                (.row ⟨76698504228, 86531900009, (.direct 2002014560937 1987910018174), (.variance 163733877679)⟩)
                (.row ⟨76698504228, 86531900009, (.direct 2723407729414 2702869768436), (.variance 151077421730)⟩)))
            (.cut 3 (13/2)
              (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3495759616946), (.variance 141236186021)⟩)
              (.row ⟨76698504228, 86531900009, (.direct 5340438828596 5295889273220), (.variance 126679959588)⟩)))
          (.cut 3 (5)
            (.cut 3 (7/2)
              (.cut 3 (11/4)
                (.row ⟨76698504228, 86531900009, (.direct 824633666698 820564556467), (.variance 206426516256)⟩)
                (.row ⟨76698504228, 86531900009, (.direct 1366046989981 1357470931153), (.variance 180933580224)⟩))
              (.cut 3 (17/4)
                (.row ⟨76698504228, 86531900009, (.direct 2002014560937 1987910018174), (.variance 163733877679)⟩)
                (.row ⟨76698504228, 86531900009, (.direct 2723407729414 2702869768436), (.variance 151077421730)⟩)))
            (.cut 3 (13/2)
              (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3495759616946), (.variance 141236186021)⟩)
              (.row ⟨76698504228, 86531900009, (.direct 5340438828596 5295889273220), (.variance 126679959588)⟩))))
        (.cut 3 (5)
          (.row ⟨76698504228, 86531900009, (.direct 824633666698 820564556467), (.variance 206426516256)⟩)
          (.row ⟨76698504228, 86531900009, (.direct 3523554676644 3495759616946), (.variance 141236186021)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid1H0Pos_checked : CutMid1H0PosTree.commonOK CutMid1H0PosBox true = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
