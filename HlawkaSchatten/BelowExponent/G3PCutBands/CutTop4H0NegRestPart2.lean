/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H0NegRestPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H0NegRestPart2Box : Box := ((((((⟨![0, 19/100, 0, -8], ![9/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H0NegRestPart2Tree : RatioRemainder :=
  .cut 3 (1/2)
    (.cut 3 (3/8)
      (.cut 3 (5/16)
        (.cut 3 (9/32)
          (.original (.row ⟨123862991199, 126950446638, (.direct 36810312175 37912872073), (.variance 488671898726)⟩))
          (.cut 3 (19/64)
            (.original (.row ⟨123862991199, 126950446638, (.direct 40103868737 41216682410), (.variance 465357958560)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 43500437793 44621269973), (.variance 455031652910)⟩))))
        (.cut 3 (11/32)
          (.cut 3 (21/64)
            (.original (.row ⟨123862991199, 126950446638, (.direct 46997848215 48124560694), (.variance 445447029174)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 50594077426 51724619227), (.variance 436517552127)⟩)))
          (.cut 3 (23/64)
            (.original (.row ⟨123862991199, 126950446638, (.direct 54287234842 55419633825), (.variance 428170307078)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 58075547817 59207903444), (.variance 420343350116)⟩)))))
      (.cut 3 (7/16)
        (.cut 3 (13/32)
          (.cut 3 (25/64)
            (.original (.row ⟨123862991199, 126950446638, (.direct 61957349610 63087826670), (.variance 412983663964)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 65931069018 67057892156), (.variance 406045562100)⟩)))
          (.cut 3 (27/64)
            (.original (.row ⟨123862991199, 126950446638, (.direct 69995221396 71116670302), (.variance 399489429209)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 74148400816 75262805983), (.variance 393280717148)⟩))))
        (.cut 3 (15/32)
          (.cut 3 (29/64)
            (.original (.row ⟨123862991199, 126950446638, (.direct 78389273202 79495012164), (.variance 387389137214)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 82716570280 83812064260), (.variance 381788004838)⟩)))
          (.cut 3 (31/64)
            (.original (.row ⟨123862991199, 126950446638, (.direct 87129084223 88212795132), (.variance 376453703784)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 91625662891 92696090634), (.variance 371365244853)⟩))))))
    (.cut 3 (5/8)
      (.cut 3 (9/16)
        (.cut 3 (17/32)
          (.cut 3 (33/64)
            (.original (.row ⟨123862991199, 126950446638, (.direct 96205205591 97260885636), (.variance 366503899985)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 100866659274 101906160453), (.variance 361852896962)⟩)))
          (.cut 0 (9/272)
            (.original (.row ⟨123862991199, 126950446638, (.direct 110431305439 110932530276), (.variance 357397163159)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 110431305439 111434279048), (.variance 356943546386)⟩))))
        (.cut 3 (19/32)
          (.original (.row ⟨123862991199, 126950446638, (.direct 120312008131 121273083243), (.variance 349018446009)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 130501749339 131415760676), (.variance 341273717280)⟩))))
      (.cut 3 (11/16)
        (.cut 3 (21/32)
          (.original (.row ⟨123862991199, 126950446638, (.direct 140994015657 141855982969), (.variance 334085249950)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 151782739331 152587849825), (.variance 327388142604)⟩)))
        (.cut 3 (23/32)
          (.original (.row ⟨123862991199, 126950446638, (.direct 162862248593 163605841836), (.variance 321127709228)⟩))
          (.original (.row ⟨123862991199, 126950446638, (.direct 174227225485 174904780337), (.variance 315257491892)⟩)))))

set_option maxRecDepth 16000 in
theorem CutTop4H0NegRestPart2_ok : CutTop4H0NegRestPart2Tree.ok CutTop4H0NegRestPart2Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
