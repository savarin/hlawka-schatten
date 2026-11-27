/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H3NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H3NegRestPart0Box : Box := (((⟨![27/68, 13/100, 0, -8], ![9/17, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutMid4H3NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3240275053229), (.variance 144071030098)⟩))
          (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 742079377775), (.variance 211933069403)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨103236350715, 110576703735, (.direct 5340438828596 4927364037065), (.variance 129095275239)⟩))
            (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3240275053229), (.variance 144071030098)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1829750918533), (.variance 167327219666)⟩))
            (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 742079377775), (.variance 211933069403)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨103236350715, 110576703735, (.direct 5340438828596 4927364037065), (.variance 129095275239)⟩))
          (.original (.row ⟨103236350715, 110576703735, (.direct 3523554676644 3240275053229), (.variance 144071030098)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨103236350715, 110576703735, (.direct 2002014560937 1829750918533), (.variance 167327219666)⟩))
          (.original (.row ⟨103236350715, 110576703735, (.direct 824633666698 742079377775), (.variance 211933069403)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 20825587808), (.variance 540212518530)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨103236350715, 110576703735, (.direct 331294831298 289741338864), (.variance 271113430154)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨103236350715, 110576703735, (.direct 151782739331 127228967781), (.variance 336314786387)⟩))
            (.cut 0 (63/136)
              (.cut 3 (-15/32)
                (.original (.row ⟨103236350715, 110576703735, (.direct 82716570280 67827885372), (.variance 396533759210)⟩))
                (.cut 2 (5/16)
                  (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 21964343513), (.variance 532733735382)⟩))
                  (.cut 3 (-23/64)
                    (.original (.row ⟨103236350715, 110576703735, (.direct 54287234842 42581496185), (.chord (.midpoint ⟨268935935457, 280867667295, 243905477793, 299210242617, 277073530184, 96314334568⟩) 43500686443 91625974997)⟩))
                    (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 21964343513), (.chord (.midpoint ⟨365447187903, 194202152006, 204795152773, 338711325803, 241797656538, 184713171203⟩) 43500686443 91625974997)⟩)))))
              (.cut 0 (135/272)
                (.cut 3 (-15/32)
                  (.original (.row ⟨103236350715, 110576703735, (.direct 82716570280 66806497484), (.variance 398112405171)⟩))
                  (.cut 2 (5/16)
                    (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 21392168990), (.variance 536428696058)⟩))
                    (.cut 2 (13/32)
                      (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 21392168990), (.chord (.midpoint ⟨294830385131, 255446227447, 227407112885, 314454657221, 267539832765, 92377130620⟩) 43500686443 65931360876)⟩))
                      (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 21392168990), (.chord (.midpoint ⟨337087627415, 217481939175, 209975763264, 332760582865, 252115214635, 175912737471⟩) 65931360876 91625974997)⟩)))))
                (.cut 3 (-15/32)
                  (.original (.row ⟨103236350715, 110576703735, (.direct 82716570280 65790840678), (.variance 399712686176)⟩))
                  (.cut 2 (5/16)
                    (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 20825587808), (.variance 540212518530)⟩))
                    (.cut 2 (13/32)
                      (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 20825587808), (.chord (.midpoint ⟨283805120823, 266056439817, 228928265773, 312970735141, 271588600296, 84363605413⟩) 43500686443 65931360876)⟩))
                      (.original (.row ⟨103236350715, 110576703735, (.direct 30541785600 20825587808), (.chord (.midpoint ⟨324779584706, 228117602006, 211884418169, 330631023251, 256597244505, 170383734694⟩) 65931360876 91625974997)⟩))))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨103236350715, 110576703735, (.direct 331294831298 289741338864), (.variance 271113430154)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨103236350715, 110576703735, (.direct 151782739331 127228967781), (.variance 336314786387)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨103236350715, 110576703735, (.direct 82716570280 65790840678), (.variance 399712686176)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutMid4H3NegRestPart0_ok : CutMid4H3NegRestPart0Tree.ok CutMid4H3NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
