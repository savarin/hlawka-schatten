/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H3NegRestPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H3NegRestPart1Box : Box := ((((⟨![27/136, 19/100, 0, -8], ![9/34, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)

set_option maxRecDepth 16000 in
def CutTop4H3NegRestPart1Tree : RatioRemainder :=
  .cut 2 (1/2)
    (.cut 2 (1/8)
      (.cut 3 (0)
        (.original (.row ⟨123862991199, 126950446638, (.direct 0 1027550858), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (1/8)
          (.cut 3 (1/16)
            (.cut 1 (39/200)
              (.cut 0 (63/272)
                (.cut 1 (77/400)
                  (.original (.row ⟨123862991199, 124642625207, (.direct 3393509060 5589303785), (.chord .universal 0 10180665226)⟩))
                  (.original (.row ⟨124642625206, 125417011706, (.direct 3393509060 5623772331), (.chord .universal 0 10180665226)⟩)))
                (.cut 3 (1/32)
                  (.original (.row ⟨123862991199, 125417011706, (.direct 1131165907 3093444491), (.chord .universal 0 10180665226)⟩))
                  (.original (.row ⟨123862991199, 125417011706, (.direct 3393509060 5975218027), (.variance 917447628162)⟩))))
              (.cut 0 (63/272)
                (.original (.row ⟨125417011705, 126950446638, (.direct 3393509060 5693232604), (.chord .universal 0 10180665226)⟩))
                (.cut 3 (1/32)
                  (.original (.row ⟨125417011705, 126950446638, (.direct 1131165907 3159342508), (.chord .universal 0 10180665226)⟩))
                  (.original (.row ⟨125417011705, 126950446638, (.direct 3393509060 6056415565), (.variance 912717666271)⟩)))))
            (.cut 3 (3/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 6452795533 9593842888), (.variance 776006384629)⟩))
              (.original (.row ⟨123862991199, 126950446638, (.direct 10180561190 13697503795), (.variance 680344517847)⟩))))
          (.cut 3 (3/16)
            (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 23412458922), (.variance 615759399401)⟩))
            (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 34922204517), (.variance 531235947379)⟩)))))
      (.cut 3 (0)
        (.cut 2 (5/16)
          (.cut 3 (-1/8)
            (.cut 2 (7/32)
              (.original (.row ⟨123862991199, 126950446638, (.direct 10180561190 6253483483), (.chord .universal 10180665226 24716235638)⟩))
              (.cut 3 (-3/16)
                (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 13963202999), (.chord (.midpoint ⟨423359104159, 151525524982, 201380828683, 342775878610, 220636738732, 225255445429⟩) 24716235638 43500686443)⟩))
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
                    (.original (.row ⟨123862991199, 126950446638, (.direct 10180561190 13697503795), (.chord (.secant 1574151333884 278088253644 61959608719 140683829642) 10180665226 16864782083)⟩)))
                  (.covered))
                (.covered)))
            (.cut 2 (7/32)
              (.cut 3 (3/16)
                (.cut 2 (11/64)
                  (.cut 3 (5/32)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 14500097491 18316390982), (.chord (.secant 1780156704053 391506126583 112355121592 205905818407) 10180665226 16864782083)⟩))
                    (.cut 2 (19/128)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 23412458922), (.chord (.secant 1995364707905 518627266529 235224342563 353064047339) 10180665226 13368036905)⟩))
                      (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 23412458922), (.chord (.secant 1759036978149 379472288797 173010694645 279859721367) 13368036905 16864782083)⟩))))
                  (.cut 3 (5/32)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 14500097491 18316390982), (.chord (.secant 1449598534844 214420002482 61821462326 140496825344) 16864782083 24716235638)⟩))
                    (.original (.row ⟨123862991199, 126950446638, (.direct 19358451269 23412458922), (.chord (.secant 1594162270331 288690669210 100479974379 190958200636) 16864782083 24716235638)⟩))))
                (.cut 2 (11/64)
                  (.cut 2 (19/128)
                    (.cut 3 (7/32)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 24716051037 28955834162), (.chord (.secant 2219504071344 658471816332 325490863255 456520088369) 10180665226 13368036905)⟩))
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 34922204517), (.chord (.secant 2452329000379 810264652584 426135838000 569468894300) 10180665226 13368036905)⟩)))
                    (.cut 3 (7/32)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 24716051037 28955834162), (.chord (.secant 1938894606376 484528425409 242810469070 361865179115) 13368036905 16864782083)⟩))
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 34922204517), (.chord (.secant 2125133223150 598766648697 320969716016 451395171180) 13368036905 16864782083)⟩))))
                  (.cut 3 (7/32)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 24716051037 28955834162), (.chord (.secant 1743735683719 370807788534 145651075856 246913625863) 16864782083 24716235638)⟩))
                    (.cut 2 (25/128)
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 34922204517), (.chord (.secant 1898202413486 460270781359 248635154491 368607384452) 16864782083 20652546629)⟩))
                      (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 34922204517), (.chord (.secant 1732139729454 364272293006 196723682897 308003261771) 20652546629 24716235638)⟩))))))
              (.cut 3 (3/16)
                (.covered)
                (.cut 2 (17/64)
                  (.cut 3 (7/32)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 24716051037 28955834162), (.chord (.secant 1491315893771 235276622070 93059863824 181509436608) 24716235638 33622326476)⟩))
                    (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 34922204517), (.chord (.secant 1605638928764 294814699522 128890055272 226417307045) 24716235638 33622326476)⟩)))
                  (.cut 3 (7/32)
                    (.covered)
                    (.original (.row ⟨123862991199, 126950446638, (.direct 30541785600 34922204517), (.chord (.secant 1426126157630 202908032593 87991796656 175001158828) 33622326476 43500686443)⟩)))))))
          (.covered))))
    (.covered)

set_option maxRecDepth 16000 in
theorem CutTop4H3NegRestPart1_ok : CutTop4H3NegRestPart1Tree.geometryOK CutTop4H3NegPowerCache CutTop4H3NegRestPart1Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
