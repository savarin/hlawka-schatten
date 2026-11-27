/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H2NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H2NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H2NegRestPart1Box : Box := ((((⟨![9/68, 19/100, 0, -8], ![27/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutTop4H2NegRestPart1Tree : RatioRemainder :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (0)
        (.original (.row ⟨123862991199, 126950446638, (.direct 0 651298572), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (1/8)
          (.cut 3 (1/16)
            (.cut 1 (39/200)
              (.cut 0 (45/272)
                (.original (.row ⟨123862991199, 125417011706, (.direct 3393509060 4944789777), (.chord .universal 0 10180665226)⟩))
                (.cut 3 (1/32)
                  (.original (.row ⟨123862991199, 125417011706, (.direct 1131165907 2537568469), (.chord .universal 0 10180665226)⟩))
                  (.original (.row ⟨123862991199, 125417011706, (.direct 3393509060 5280252266), (.chord .universal 0 10180665226)⟩))))
              (.cut 0 (45/272)
                (.original (.row ⟨125417011705, 126950446638, (.direct 3393509060 4992079111), (.chord .universal 0 10180665226)⟩))
                (.original (.row ⟨125417011705, 126950446638, (.direct 3393509060 5338406430), (.chord .universal 0 10180665226)⟩))))
            (.cut 3 (3/32)
              (.cut 3 (5/64)
                (.original (.row ⟨123862991199, 126950446638, (.direct 4833349683 6974255551), (.variance 803108463218)⟩))
                (.original (.row ⟨123862991199, 126950446638, (.direct 6452795533 8766024539), (.variance 743548991703)⟩)))
              (.original (.row ⟨123862991199, 126950446638, (.direct 10180561190 12782493823), (.variance 696780189186)⟩))))
          (.cut 3 (3/16)
            (.cut 3 (5/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 14500097491 17331697519), (.variance 626941716170)⟩))
              (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 22372460883), (.variance 576361617693)⟩)))
            (.cut 3 (7/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 24716051037 27872805152), (.variance 537444892522)⟩))
              (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 33806907894), (.variance 506240881315)⟩))))))
      (.cut 3 (0)
        (.cut 2 (5/16)
          (.cut 3 (-1/8)
            (.cut 2 (7/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 10180561190 7168719696), (.chord .universal 10180665226 24716235638)⟩))
              (.cut 3 (-3/16)
                (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 15250780141), (.chord (.midpoint ⟨443061506049, 138374007533, 200346902647, 344030034848, 213365816605, 230122246536⟩) 24716235638 43500686443)⟩))
                (.covered)))
            (.covered))
          (.covered))
        (.cut 2 (5/16)
          (.cut 3 (1/8)
            (.cut 3 (1/16)
              (.covered)
              (.cut 2 (7/32)
                (.cut 2 (11/64)
                  (.cut 3 (3/32)
                    (.covered)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 10180561190 12782493823), (.chord (.secant 1586369155029 284550116420 69550638746 128426457407) 10180665226 16864782083)⟩)))
                  (.covered))
                (.covered)))
            (.cut 2 (7/32)
              (.cut 3 (3/16)
                (.cut 2 (11/64)
                  (.cut 3 (5/32)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 14500097491 17331697519), (.chord (.secant 1794540863081 399750658688 122155624658 192229491055) 10180665226 16864782083)⟩))
                    (.cut 2 (19/128)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 22372460883), (.chord (.secant 2012035511929 528786879168 246296843326 334382796560) 10180665226 13368036905)⟩))
                      (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 22372460883), (.chord (.secant 1781500777995 392274853779 184936877226 265051812606) 13368036905 16864782083)⟩))))
                  (.cut 3 (5/32)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 14500097491 17331697519), (.chord (.secant 1473880584770 226499605187 71738449887 131164983290) 16864782083 24716235638)⟩))
                    (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 22372460883), (.chord (.secant 1620427789841 302751780959 112569150193 180854229914) 16864782083 24716235638)⟩))))
                (.cut 2 (11/64)
                  (.cut 2 (19/128)
                    (.cut 3 (7/32)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 24716051037 27872805152), (.chord (.secant 2238577633671 670674408689 338641804854 436705006351) 10180665226 13368036905)⟩))
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 33806907894), (.chord (.secant 2473917691431 824633666698 441403735746 548768466540) 10180665226 13368036905)⟩)))
                    (.cut 3 (7/32)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 24716051037 27872805152), (.chord (.secant 1963570186406 499367596990 256830289084 346158557684) 13368036905 16864782083)⟩))
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 33806907894), (.chord (.secant 2152096213652 615708518680 337077699222 434986771659) 13368036905 16864782083)⟩))))
                  (.cut 3 (7/32)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 24716051037 27872805152), (.chord (.secant 1772039142975 386870686725 159808823524 236196400688) 16864782083 24716235638)⟩))
                    (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 33806907894), (.chord (.secant 1928597329841 478364539818 212889146855 296807216940) 16864782083 24716235638)⟩)))))
              (.cut 3 (3/16)
                (.covered)
                (.cut 2 (17/64)
                  (.cut 3 (7/32)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 24716051037 27872805152), (.chord (.secant 1523907223045 251906774557 106521485682 173631064175) 24716235638 33622326476)⟩))
                    (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 33806907894), (.chord (.secant 1640009514264 313338656495 144281770164 218186920065) 24716235638 33622326476)⟩)))
                  (.cut 3 (7/32)
                    (.covered)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 33806907894), (.chord (.secant 1462625680250 220879462846 102361881728 168639775602) 33622326476 43500686443)⟩)))))))
          (.covered))))
    (.covered)

set_option maxRecDepth 16000 in
theorem CutTop4H2NegRestPart1_ok : CutTop4H2NegRestPart1Tree.geometryOK CutTop4H2NegPowerCache CutTop4H2NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
