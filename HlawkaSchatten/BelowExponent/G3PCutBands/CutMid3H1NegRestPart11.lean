/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H1NegRestPart11`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H1NegRestPart11Box : Box := ((((⟨![9/68, 11/100, 0, -8], ![9/34, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid3H1NegRestPart11Tree : RatioRemainder :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.cut 3 (5/16)
            (.cut 1 (3/25)
              (.original (.row ⟨95281442640, 99345187400, (.direct 43500437793 46091267487), (.variance 484060181085)⟩))
              (.original (.row ⟨99345187399, 103236350716, (.direct 43500437793 46324833282), (.variance 483621994154)⟩)))
            (.cut 0 (27/136)
              (.original (.row ⟨95281442640, 103236350716, (.direct 58075547817 60207363522), (.variance 442351015994)⟩))
              (.original (.row ⟨95281442640, 103236350716, (.direct 58075547817 60924160219), (.variance 440830248796)⟩))))
          (.cut 3 (7/16)
            (.original (.row ⟨95281442640, 103236350716, (.direct 74148400816 76948441491), (.variance 410802886692)⟩))
            (.original (.row ⟨95281442640, 103236350716, (.direct 91625662891 94312731089), (.variance 385807837714)⟩))))
        (.cut 3 (5/8)
          (.original (.row ⟨95281442640, 103236350716, (.direct 130501749339 132793187403), (.variance 365338508702)⟩))
          (.cut 3 (11/16)
            (.original (.row ⟨95281442640, 103236350716, (.direct 151782739331 153800199397), (.variance 333446481794)⟩))
            (.original (.row ⟨95281442640, 103236350716, (.direct 174227225485 175924376630), (.variance 320662195138)⟩)))))
      (.cut 0 (27/136)
        (.cut 3 (1/2)
          (.cut 3 (3/8)
            (.cut 0 (45/272)
              (.cut 3 (5/16)
                (.cut 1 (3/25)
                  (.original (.row ⟨95281442640, 99345187400, (.direct 43500437793 45113322837), (.variance 484060181085)⟩))
                  (.cut 3 (9/32)
                    (.original (.row ⟨99345187399, 103236350716, (.direct 36810312175 38540057205), (.variance 483621994154)⟩))
                    (.original (.row ⟨99345187399, 103236350716, (.direct 43500437793 45258101087), (.variance 461250749297)⟩))))
                (.original (.row ⟨95281442640, 103236350716, (.direct 58075547817 59850140499), (.variance 442351015994)⟩)))
              (.cut 3 (5/16)
                (.cut 1 (3/25)
                  (.original (.row ⟨95281442640, 99345187400, (.direct 43500437793 45438444075), (.variance 482930229520)⟩))
                  (.original (.row ⟨99345187399, 103236350716, (.direct 43500437793 45612659064), (.variance 482387046421)⟩)))
                (.original (.row ⟨95281442640, 103236350716, (.direct 58075547817 60207363522), (.variance 441588400391)⟩))))
            (.original (.row ⟨95281442640, 103236350716, (.direct 91625662891 93638357063), (.variance 410802886692)⟩)))
          (.original (.row ⟨95281442640, 103236350716, (.direct 174227225485 175499581465), (.variance 365338508702)⟩)))
        (.cut 3 (1/2)
          (.cut 3 (3/8)
            (.cut 0 (63/272)
              (.cut 3 (5/16)
                (.cut 1 (3/25)
                  (.original (.row ⟨95281442640, 99345187400, (.direct 43500437793 45764426162), (.variance 481809220595)⟩))
                  (.original (.row ⟨99345187399, 103236350716, (.direct 43500437793 45968237153), (.variance 481162784527)⟩)))
                (.original (.row ⟨95281442640, 103236350716, (.direct 58075547817 60565370500), (.variance 440830248796)⟩)))
              (.cut 3 (5/16)
                (.cut 1 (3/25)
                  (.original (.row ⟨95281442640, 99345187400, (.direct 43500437793 46091267487), (.variance 480697034191)⟩))
                  (.original (.row ⟨99345187399, 103236350716, (.direct 43500437793 46324833282), (.variance 479949051625)⟩)))
                (.original (.row ⟨95281442640, 103236350716, (.direct 58075547817 60924160219), (.variance 440076516797)⟩))))
            (.original (.row ⟨95281442640, 103236350716, (.direct 91625662891 94312731089), (.variance 409727110152)⟩)))
          (.original (.row ⟨95281442640, 103236350716, (.direct 174227225485 175924376630), (.variance 364760529272)⟩)))))
    (.cut 3 (1/2)
      (.original (.row ⟨95281442640, 103236350716, (.direct 91625662891 94312731089), (.chord (.secant 1474708470903 226914435884 155312464 31667988849) 91625974997 274877906944)⟩))
      (.original (.row ⟨95281442640, 103236350716, (.direct 174227225485 175924376630), (.variance 365338508702)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid3H1NegRestPart11_ok : CutMid3H1NegRestPart11Tree.ok CutMid3H1NegRestPart11Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
