/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H1NegRestPart9`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H1NegRestPart9Box : Box := ((((((⟨![9/68, 9/100, 0, -8], ![9/34, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid2H1NegRestPart9Tree : RatioRemainder :=
  .cut 2 (5/16)
    (.cut 3 (0)
      (.cut 2 (7/32)
        (.cut 1 (1/10)
          (.cut 3 (-1/8)
            (.cut 2 (11/64)
              (.original (.row ⟨86531900008, 91020629598, (.direct 10180561190 8232971135), (.variance 688818348335)⟩))
              (.original (.row ⟨86531900008, 91020629598, (.direct 10180561190 8232971135), (.chord (.midpoint ⟨451612059741, 132869852188, 197027428502, 348132473063, 210193273254, 142715130703⟩) 16864782083 24716235638)⟩)))
            (.covered))
          (.cut 3 (-1/8)
            (.cut 3 (-3/16)
              (.original (.row ⟨91020629597, 95281442641, (.direct 19358451269 16451461775), (.variance 574615284054)⟩))
              (.cut 2 (11/64)
                (.original (.row ⟨91020629597, 95281442641, (.direct 10180561190 8035890059), (.chord (.midpoint ⟨387154314439, 177472984397, 221733512942, 320142471739, 233890900151, 136306054881⟩) 10180665226 16864782083)⟩))
                (.original (.row ⟨91020629597, 95281442641, (.direct 10180561190 8035890059), (.chord (.midpoint ⟨455586053757, 130352795609, 195479080760, 350086695561, 208714807771, 221715229042⟩) 16864782083 24716235638)⟩))))
            (.covered)))
        (.cut 1 (1/10)
          (.cut 3 (-1/8)
            (.cut 3 (-3/16)
              (.original (.row ⟨86531900008, 91020629598, (.direct 19358451269 16722064399), (.chord (.midpoint ⟨427122308935, 148962250757, 206495074716, 336730577474, 219251797652, 209402986372⟩) 24716235638 43500686443)⟩))
              (.covered))
            (.covered))
          (.cut 3 (-1/8)
            (.cut 3 (-3/16)
              (.original (.row ⟨91020629597, 95281442641, (.direct 19358451269 16451461775), (.chord (.midpoint ⟨429997754426, 147020133787, 205389473757, 338015637346, 218192424701, 210214779592⟩) 24716235638 43500686443)⟩))
              (.covered))
            (.covered))))
      (.cut 2 (7/32)
        (.cut 3 (1/8)
          (.cut 3 (1/16)
            (.covered)
            (.cut 3 (3/32)
              (.covered)
              (.cut 2 (11/64)
                (.cut 3 (7/64)
                  (.covered)
                  (.original (.row ⟨86531900008, 95281442641, (.direct 10180561190 11974917917), (.chord (.secant 1547799205681 264276470582 65346947232 145250217610) 10180665226 16864782083)⟩)))
                (.covered))))
          (.cut 2 (11/64)
            (.cut 3 (3/16)
              (.cut 3 (5/32)
                (.cut 2 (19/128)
                  (.original (.row ⟨86531900008, 95281442641, (.direct 14500097491 16458206969), (.chord (.secant 1755597699798 377520771068 126933520455 224006495283) 10180665226 13368036905)⟩))
                  (.original (.row ⟨86531900008, 95281442641, (.direct 14500097491 16458206969), (.chord (.secant 1574564148789 278305991851 89980694104 177560843880) 13368036905 16864782083)⟩)))
                (.cut 2 (19/128)
                  (.original (.row ⟨86531900008, 95281442641, (.direct 19358451269 21446622461), (.chord (.secant 1972900967319 505003673217 202006656007 314229312224) 10180665226 13368036905)⟩))
                  (.original (.row ⟨86531900008, 95281442641, (.direct 19358451269 21446622461), (.chord (.secant 1749982376693 374339486443 147432573398 249076907015) 13368036905 16864782083)⟩))))
              (.cut 3 (7/32)
                (.cut 2 (19/128)
                  (.original (.row ⟨86531900008, 95281442641, (.direct 24716051037 26906112949), (.chord (.secant 2199422597984 645672530109 289210673028 415242521462) 10180665226 13368036905)⟩))
                  (.original (.row ⟨86531900008, 95281442641, (.direct 24716051037 26906112949), (.chord (.secant 1932145932027 480486788850 214713778959 329146106016) 13368036905 16864782083)⟩)))
                (.cut 2 (19/128)
                  (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 32809388292), (.chord (.secant 2434903642097 798701008373 387444791572 526281246954) 10180665226 13368036905)⟩))
                  (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 32809388292), (.chord (.secant 2120881996636 596104216208 290890696064 417162053863) 13368036905 16864782083)⟩)))))
            (.cut 3 (3/16)
              (.cut 3 (5/32)
                (.covered)
                (.original (.row ⟨86531900008, 95281442641, (.direct 19358451269 21446622461), (.chord (.secant 1594135739251 288676548304 84087307341 169953986599) 16864782083 24716235638)⟩)))
              (.cut 3 (7/32)
                (.original (.row ⟨86531900008, 95281442641, (.direct 24716051037 26906112949), (.chord (.secant 1745902677001 372032071321 127405275944 224588159583) 16864782083 24716235638)⟩))
                (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 32809388292), (.chord (.secant 1902703554428 462940675282 177021948153 284644766892) 16864782083 24716235638)⟩))))))
        (.cut 3 (1/8)
          (.covered)
          (.cut 3 (3/16)
            (.covered)
            (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 32809388292), (.chord (.secant 1620839623366 302973536078 52416297927 127606357459) 24716235638 43500686443)⟩))))))
    (.covered)

set_option maxRecDepth 16000 in
theorem CutMid2H1NegRestPart9_ok : CutMid2H1NegRestPart9Tree.ok CutMid2H1NegRestPart9Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
