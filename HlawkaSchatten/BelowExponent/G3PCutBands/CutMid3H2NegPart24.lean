/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H2NegPart24`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H2NegPart24Box : Box := ((((⟨![9/34, 11/100, 0, -8], ![27/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutMid3H2NegPart24Tree : CertTree :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (1/2)
        (.cut 3 (3/8)
          (.cut 3 (5/16)
            (.cut 1 (3/25)
              (.row ⟨95281442640, 99345187400, (.direct 43500437793 47407193324), (.variance 479593552461)⟩)
              (.row ⟨99345187399, 103236350716, (.direct 43500437793 47761357255), (.variance 478745694101)⟩))
            (.row ⟨95281442640, 103236350716, (.direct 58075547817 62367122390), (.variance 439327160602)⟩))
          (.row ⟨95281442640, 103236350716, (.direct 91625662891 95666828978), (.variance 408660878271)⟩))
        (.cut 3 (5/8)
          (.row ⟨95281442640, 103236350716, (.direct 130501749339 133944266074), (.variance 364185655530)⟩)
          (.row ⟨95281442640, 103236350716, (.direct 174227225485 176775103434), (.variance 332811858538)⟩)))
      (.cut 0 (45/136)
        (.cut 3 (1/2)
          (.cut 3 (3/8)
            (.cut 0 (81/272)
              (.cut 3 (5/16)
                (.cut 1 (3/25)
                  (.row ⟨95281442640, 99345187400, (.direct 43500437793 46418966450), (.variance 479593552461)⟩)
                  (.row ⟨99345187399, 103236350716, (.direct 43500437793 46682445394), (.variance 478745694101)⟩))
                (.row ⟨95281442640, 103236350716, (.direct 58075547817 61283731467), (.variance 439327160602)⟩))
              (.cut 3 (5/16)
                (.row ⟨95281442640, 103236350716, (.direct 43500437793 47041071444), (.variance 478498659770)⟩)
                (.row ⟨95281442640, 103236350716, (.direct 58075547817 61644083042), (.variance 438582137033)⟩)))
            (.row ⟨95281442640, 103236350716, (.direct 91625662891 94988889506), (.variance 408660878271)⟩))
          (.row ⟨95281442640, 103236350716, (.direct 174227225485 176349550700), (.variance 364185655530)⟩))
        (.cut 3 (1/2)
          (.cut 3 (3/8)
            (.cut 0 (99/272)
              (.cut 3 (5/16)
                (.row ⟨95281442640, 103236350716, (.direct 43500437793 47400709403), (.variance 477412242643)⟩)
                (.row ⟨95281442640, 103236350716, (.direct 58075547817 62005213746), (.variance 437841403511)⟩))
              (.cut 3 (5/16)
                (.row ⟨95281442640, 103236350716, (.direct 43500437793 47761357255), (.variance 476334189713)⟩)
                (.row ⟨95281442640, 103236350716, (.direct 58075547817 62367122390), (.variance 437104918044)⟩)))
            (.row ⟨95281442640, 103236350716, (.direct 91625662891 95666828978), (.variance 407604047421)⟩))
          (.row ⟨95281442640, 103236350716, (.direct 174227225485 176775103434), (.variance 363613859102)⟩))))
    (.cut 0 (45/136)
      (.row ⟨95281442640, 103236350716, (.direct 174227225485 176349550700), (.variance 479593552461)⟩)
      (.row ⟨95281442640, 103236350716, (.direct 174227225485 176775103434), (.variance 477412242643)⟩))

set_option maxRecDepth 16000 in
theorem CutMid3H2NegPart24_checked : CutMid3H2NegPart24Tree.commonOK CutMid3H2NegPart24Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
