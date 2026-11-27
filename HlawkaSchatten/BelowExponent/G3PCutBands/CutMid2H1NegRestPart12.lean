/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1NegRestPart12`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1NegRestPart12Box : Box := ((⟨![9/68, 9/100, 0, -8], ![9/34, 11/100, 1, 8]⟩ : Box)).upperChild 3 (3/4)

set_option maxRecDepth 16000 in
def CutMid2H1NegRestPart12Tree : RatioRemainder :=
  .cut 3 (2)
    (.cut 3 (5/4)
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.original (.cone))
          (.original (.row ⟨86531900008, 95281442641, .zero, (.variance 309470879084)⟩)))
        (.original (.row ⟨86531900008, 95281442641, .zero, (.variance 309470879084)⟩)))
      (.cut 2 (1/2)
        (.cut 2 (1/8)
          (.cut 3 (13/8)
            (.original (.row ⟨86531900008, 95281442641, (.direct 391506126583 389596297645), (.variance 250885320593)⟩))
            (.original (.row ⟨86531900008, 95281442641, (.direct 593382169971 587820406912), (.variance 225268265636)⟩)))
          (.original (.row ⟨86531900008, 95281442641, (.direct 391506126583 389596297645), (.variance 250885320593)⟩)))
        (.original (.row ⟨86531900008, 95281442641, (.direct 391506126583 389596297645), (.variance 250885320593)⟩))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (5)
          (.cut 3 (7/2)
            (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 814591087966), (.variance 206821830431)⟩))
            (.original (.row ⟨86531900008, 95281442641, (.direct 2002014560937 1967220860641), (.variance 164183048415)⟩)))
          (.original (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3454999282665), (.variance 141670611726)⟩)))
        (.cut 3 (5)
          (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 814591087966), (.variance 206821830431)⟩))
          (.original (.row ⟨86531900008, 95281442641, (.direct 3523554676644 3454999282665), (.variance 141670611726)⟩))))
      (.original (.row ⟨86531900008, 95281442641, (.direct 824633666698 814591087966), (.variance 206821830431)⟩)))

set_option maxRecDepth 16000 in
theorem CutMid2H1NegRestPart12_ok : CutMid2H1NegRestPart12Tree.ok CutMid2H1NegRestPart12Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
