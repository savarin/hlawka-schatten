/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H2NegRestPart14`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H2NegRestPart14Box : Box := (((((((((⟨![9/34, 9/100, 0, -8], ![27/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).lowerChild 3 (1/8)).upperChild 3 (1/16)

set_option maxRecDepth 16000 in
def CutMid2H2NegRestPart14Tree : RatioRemainder :=
  .cut 1 (1/10)
    (.cut 3 (3/32)
      (.cut 1 (19/200)
        (.cut 0 (45/136)
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨86531900008, 88806993133, (.direct 4833349683 6407826967), (.variance 809059579663)⟩))
              (.original (.row ⟨86531900008, 88806993133, (.direct 4833349683 6407826967), (.chord (.secant 1761682724908 380975105519 33030532014 120247104432) 3393555298 10180665226)⟩)))
            (.original (.row ⟨86531900008, 88806993133, (.direct 6452795533 8158750838), (.variance 748038479116)⟩)))
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨86531900008, 88806993133, (.direct 4833349683 6742010128), (.variance 796186301980)⟩))
              (.original (.row ⟨86531900008, 88806993133, (.direct 4833349683 6742010128), (.chord (.secant 1746572976392 372410957148 24918193021 127842719678) 3393555298 10180665226)⟩)))
            (.original (.row ⟨86531900008, 88806993133, (.direct 6452795533 8517380368), (.variance 738300743312)⟩))))
        (.cut 0 (45/136)
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨88806993132, 91020629598, (.direct 4833349683 6499770015), (.variance 805992707354)⟩))
              (.original (.row ⟨88806993132, 91020629598, (.direct 4833349683 6499770015), (.chord (.secant 1773358077259 387622993657 34124617091 122003815456) 3393555298 10180665226)⟩)))
            (.original (.row ⟨88806993132, 91020629598, (.direct 6452795533 8257523583), (.variance 745727454001)⟩)))
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨88806993132, 91020629598, (.direct 4833349683 6854479330), (.variance 792561458794)⟩))
              (.original (.row ⟨88806993132, 91020629598, (.direct 4833349683 6854479330), (.chord (.secant 1760542443483 380327245058 26154339450 130090031840) 3393555298 10180665226)⟩)))
            (.original (.row ⟨88806993132, 91020629598, (.direct 6452795533 8637849345), (.variance 735541239492)⟩)))))
      (.cut 0 (45/136)
        (.cut 1 (19/200)
          (.original (.row ⟨86531900008, 88806993133, (.direct 10180561190 12106445432), (.variance 700310933825)⟩))
          (.original (.row ⟨88806993132, 91020629598, (.direct 10180561190 12216704597), (.variance 698494885946)⟩)))
        (.original (.row ⟨86531900008, 91020629598, (.direct 10180561190 12640161160), (.variance 692638010584)⟩))))
    (.cut 3 (3/32)
      (.cut 1 (21/200)
        (.cut 0 (45/136)
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨91020629597, 93177423805, (.direct 4833349683 6592684610), (.variance 802949280297)⟩))
              (.original (.row ⟨91020629597, 93177423805, (.direct 4833349683 6592684610), (.chord (.secant 1785123705303 394348646731 35237666380 123779232056) 3393555298 10180665226)⟩)))
            (.original (.row ⟨91020629597, 93177423805, (.direct 6452795533 8357259012), (.variance 743428618673)⟩)))
          (.cut 3 (5/64)
            (.original (.row ⟨91020629597, 93177423805, (.direct 4833349683 6968232718), (.variance 788973630649)⟩))
            (.original (.row ⟨91020629597, 93177423805, (.direct 6452795533 8759582288), (.variance 732802337435)⟩))))
        (.cut 0 (45/136)
          (.cut 3 (5/64)
            (.cut 2 (1/16)
              (.original (.row ⟨93177423804, 95281442641, (.direct 4833349683 6686580508), (.variance 799928927202)⟩))
              (.original (.row ⟨93177423804, 95281442641, (.direct 4833349683 6686580508), (.chord (.secant 1796980503493 401152827702 36369823098 125573541278) 3393555298 10180665226)⟩)))
            (.original (.row ⟨93177423804, 95281442641, (.direct 6452795533 8457966879), (.variance 741141824704)⟩)))
          (.cut 3 (5/64)
            (.original (.row ⟨93177423804, 95281442641, (.direct 4833349683 7083282977), (.variance 785422078687)⟩))
            (.original (.row ⟨93177423804, 95281442641, (.direct 6452795533 8882591906), (.variance 730083716718)⟩)))))
      (.cut 0 (45/136)
        (.cut 1 (21/200)
          (.original (.row ⟨91020629597, 93177423805, (.direct 10180561190 12327917024), (.variance 696685362278)⟩))
          (.original (.row ⟨93177423804, 95281442641, (.direct 10180561190 12440092344), (.variance 694882298628)⟩)))
        (.original (.row ⟨91020629597, 95281442641, (.direct 10180561190 12911777146), (.variance 688281446002)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid2H2NegRestPart14_ok : CutMid2H2NegRestPart14Tree.ok CutMid2H2NegRestPart14Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
