/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H2NegRestPart16`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H2NegRestPart16Box : Box := ((((((⟨![9/34, 9/100, 0, -8], ![27/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid2H2NegRestPart16Tree : RatioRemainder :=
  .cut 2 (5/16)
    (.cut 3 (0)
      (.cut 1 (1/10)
        (.cut 2 (7/32)
          (.cut 3 (-1/8)
            (.cut 2 (11/64)
              (.original (.row ⟨86531900008, 91020629598, (.direct 10180561190 7317413934), (.variance 710414223290)⟩))
              (.original (.row ⟨86531900008, 91020629598, (.direct 10180561190 7317413934), (.chord (.midpoint ⟨402152990669, 166435602476, 203141262953, 340665600250, 228413291167, 119025105355⟩) 16864782083 24716235638)⟩)))
            (.covered))
          (.cut 3 (-1/8)
            (.original (.row ⟨86531900008, 91020629598, (.direct 10180561190 7317413934), (.chord (.midpoint ⟨474137324300, 118941509209, 173888439259, 380399362550, 201775774551, 189889359748⟩) 24716235638 43500686443)⟩))
            (.covered)))
        (.cut 3 (-1/8)
          (.cut 2 (7/32)
            (.cut 3 (-3/16)
              (.original (.row ⟨91020629597, 95281442641, (.direct 19358451269 15064281775), (.variance 588023780614)⟩))
              (.original (.row ⟨91020629597, 95281442641, (.direct 10180561190 7035160075), (.chord (.midpoint ⟨407869845945, 162337110178, 200865844844, 343399176510, 226321025571, 117910599297⟩) 10180665226 24716235638)⟩)))
            (.cut 3 (-3/16)
              (.original (.row ⟨91020629597, 95281442641, (.direct 19358451269 15064281775), (.chord (.midpoint ⟨378241690227, 184231524341, 212597093023, 329844251236, 237139549990, 191626389568⟩) 24716235638 43500686443)⟩))
              (.covered)))
          (.covered)))
      (.cut 3 (1/8)
        (.cut 2 (7/32)
          (.cut 3 (1/16)
            (.covered)
            (.cut 2 (11/64)
              (.cut 3 (3/32)
                (.covered)
                (.cut 2 (19/128)
                  (.original (.row ⟨86531900008, 95281442641, (.direct 10180561190 12911777146), (.chord (.secant 1483635035263 231399565363 43097930586 158922395469) 10180665226 13368036905)⟩))
                  (.covered)))
              (.covered)))
          (.covered))
        (.cut 2 (7/32)
          (.cut 0 (45/136)
            (.cut 2 (11/64)
              (.cut 3 (3/16)
                (.cut 3 (5/32)
                  (.original (.row ⟨86531900008, 95281442641, (.direct 14500097491 16961880940), (.chord (.secant 1664628742291 326771211345 80252464459 189476068536) 10180665226 16864782083)⟩))
                  (.original (.row ⟨86531900008, 95281442641, (.direct 19358451269 21980874591), (.chord (.secant 1877009635945 447745691001 135313059583 262060829298) 10180665226 16864782083)⟩)))
                (.cut 1 (1/10)
                  (.original (.row ⟨86531900008, 91020629598, (.direct 30541785600 33109415816), (.variance 538745175274)⟩))
                  (.original (.row ⟨91020629597, 95281442641, (.direct 30541785600 33385556009), (.variance 537409808706)⟩))))
              (.cut 3 (3/16)
                (.original (.row ⟨86531900008, 95281442641, (.direct 19358451269 21980874591), (.chord (.secant 1500048926228 239704568189 38734747639 129286225683) 16864782083 24716235638)⟩))
                (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 33385556009), (.chord (.secant 1800926712973 403423231492 113587377996 234026784732) 16864782083 24716235638)⟩))))
            (.cut 1 (1/10)
              (.cut 3 (3/16)
                (.cut 2 (11/64)
                  (.cut 3 (5/32)
                    (.original (.row ⟨86531900008, 91020629598, (.direct 14500097491 17178061126), (.chord (.secant 1618201005937 301553429469 66792014592 195540178945) 10180665226 16864782083)⟩))
                    (.original (.row ⟨86531900008, 91020629598, (.direct 19358451269 22209849048), (.chord (.secant 1828100076427 419134735627 118653347787 268643698795) 10180665226 16864782083)⟩)))
                  (.original (.row ⟨86531900008, 91020629598, (.direct 19358451269 22209849048), (.chord (.secant 1452714192163 215960384328 28013630698 133423982778) 16864782083 24716235638)⟩)))
                (.original (.row ⟨86531900008, 91020629598, (.direct 30541785600 33632031987), (.variance 535904457966)⟩)))
              (.cut 3 (3/16)
                (.cut 2 (11/64)
                  (.cut 3 (5/32)
                    (.original (.row ⟨91020629597, 95281442641, (.direct 14500097491 17471136443), (.chord (.secant 1630729476174 308310508241 69207303204 199119017114) 10180665226 16864782083)⟩))
                    (.original (.row ⟨91020629597, 95281442641, (.direct 19358451269 22519962788), (.chord (.secant 1840718046610 426475734615 121526385149 272521195561) 10180665226 16864782083)⟩)))
                  (.original (.row ⟨91020629597, 95281442641, (.direct 19358451269 22519962788), (.chord (.secant 1461142848059 220141719663 29393959011 135865950689) 16864782083 24716235638)⟩)))
                (.original (.row ⟨91020629597, 95281442641, (.direct 30541785600 33965417195), (.variance 534266685979)⟩)))))
          (.cut 3 (3/16)
            (.covered)
            (.cut 2 (17/64)
              (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 33965417195), (.chord (.secant 1532896868250 256543651827 51349060977 172036151101) 24716235638 33622326476)⟩))
              (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 33965417195), (.chord (.secant 1359540623643 171188529420 27758258140 132969189484) 33622326476 43500686443)⟩)))))))
    (.covered)

set_option maxRecDepth 16000 in
theorem CutMid2H2NegRestPart16_ok : CutMid2H2NegRestPart16Tree.ok CutMid2H2NegRestPart16Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
