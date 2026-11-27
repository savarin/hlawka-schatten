/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0NegRestPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0NegRestPart6Box : Box := ((((((⟨![0, 9/100, 0, -8], ![9/68, 11/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid2H0NegRestPart6Tree : RatioRemainder :=
  .cut 2 (5/16)
    (.cut 3 (0)
      (.cut 2 (7/32)
        (.cut 1 (1/10)
          (.cut 3 (-1/8)
            (.cut 0 (9/136)
              (.original (.row ⟨86531900008, 91020629598, (.direct 10180561190 9679512744), (.variance 660232333763)⟩))
              (.original (.row ⟨86531900008, 91020629598, (.direct 10180561190 9187759033), (.variance 669308455297)⟩)))
            (.covered))
          (.cut 3 (-1/8)
            (.cut 1 (21/200)
              (.original (.row ⟨91020629597, 93177423805, (.direct 10180561190 9136412464), (.chord .universal 10180665226 24716235638)⟩))
              (.cut 0 (9/136)
                (.original (.row ⟨93177423804, 95281442641, (.direct 10180561190 9627028444), (.chord .universal 10180665226 24716235638)⟩))
                (.original (.row ⟨93177423804, 95281442641, (.direct 10180561190 9084901347), (.variance 671284535891)⟩))))
            (.covered)))
        (.cut 1 (1/10)
          (.cut 3 (-1/8)
            (.cut 3 (-3/16)
              (.original (.row ⟨86531900008, 91020629598, (.direct 19358451269 18022538526), (.chord (.midpoint ⟨482660063990, 113882895607, 198565591243, 346216928321, 198565048750, 227702871141⟩) 24716235638 43500686443)⟩))
              (.covered))
            (.covered))
          (.cut 3 (-1/8)
            (.cut 3 (-3/16)
              (.original (.row ⟨91020629597, 95281442641, (.direct 19358451269 17883226126), (.chord (.midpoint ⟨484163136510, 113002589625, 197997721147, 346921160488, 197997175442, 227702871141⟩) 24716235638 43500686443)⟩))
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
                  (.original (.row ⟨86531900008, 95281442641, (.direct 10180561190 11064363690), (.chord (.secant 1612960487976 298737760780 92793601138 134282444165) 10180665226 16864782083)⟩)))
                (.covered))))
          (.cut 3 (3/16)
            (.cut 2 (11/64)
              (.cut 3 (5/32)
                (.cut 2 (19/128)
                  (.original (.row ⟨86531900008, 95281442641, (.direct 14500097491 15467781787), (.chord (.secant 1825507661930 417630025983 159642950444 209337960765) 10180665226 13368036905)⟩))
                  (.original (.row ⟨86531900008, 95281442641, (.direct 14500097491 15467781787), (.chord (.secant 1648679074677 318053541655 120688224722 165933692783) 13368036905 16864782083)⟩)))
                (.cut 2 (19/128)
                  (.original (.row ⟨86531900008, 95281442641, (.direct 19358451269 20392752152), (.chord (.secant 2047610612398 550604199647 240964656490 298158423466) 10180665226 13368036905)⟩))
                  (.original (.row ⟨86531900008, 95281442641, (.direct 19358451269 20392752152), (.chord (.secant 1828423213862 419322378307 184174329510 236338122957) 13368036905 16864782083)⟩))))
              (.cut 3 (5/32)
                (.covered)
                (.original (.row ⟨86531900008, 95281442641, (.direct 19358451269 20392752152), (.chord (.secant 1674837162680 332380045038 116539215032 161261863507) 16864782083 24716235638)⟩))))
            (.cut 2 (11/64)
              (.cut 3 (7/32)
                (.cut 2 (19/128)
                  (.original (.row ⟨86531900008, 95281442641, (.direct 24716051037 25802599265), (.chord (.secant 2278985973689 696670042953 334008561193 398058022940) 10180665226 13368036905)⟩))
                  (.original (.row ⟨86531900008, 95281442641, (.direct 24716051037 25802599265), (.chord (.secant 2014940369252 530561407802 257042156069 315524642703) 13368036905 16864782083)⟩)))
                (.cut 2 (19/128)
                  (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 31668201037), (.chord (.secant 2519377144535 855041259588 437804584641 508223246841) 10180665226 13368036905)⟩))
                  (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 31668201037), (.chord (.secant 2208060288982 651171812258 338499594466 402848200843) 13368036905 16864782083)⟩))))
              (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 31668201037), (.chord (.secant 1991302212972 516157800020 165037005890 215293719798) 16864782083 24716235638)⟩)))))
        (.cut 3 (1/8)
          (.covered)
          (.cut 3 (3/16)
            (.covered)
            (.original (.row ⟨86531900008, 95281442641, (.direct 30541785600 31668201037), (.chord (.secant 1710579885407 352193147258 82408612652 122325448583) 24716235638 43500686443)⟩))))))
    (.covered)

set_option maxRecDepth 16000 in
theorem CutMid2H0NegRestPart6_ok : CutMid2H0NegRestPart6Tree.geometryOK CutMid2H0NegPowerCache CutMid2H0NegRestPart6Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
