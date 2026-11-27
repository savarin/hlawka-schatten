/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid3H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid3H0NegRestPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid3H0NegRestPart6Box : Box := ((((((⟨![0, 11/100, 0, -8], ![9/68, 13/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutMid3H0NegRestPart6Tree : RatioRemainder :=
  .cut 2 (5/16)
    (.cut 3 (0)
      (.cut 1 (3/25)
        (.cut 2 (7/32)
          (.cut 3 (-1/8)
            (.cut 1 (23/200)
              (.cut 0 (9/136)
                (.original (.row ⟨95281442640, 97336292160, (.direct 10180561190 9600617403), (.chord .universal 10180665226 24716235638)⟩))
                (.original (.row ⟨95281442640, 97336292160, (.direct 10180561190 9033225388), (.variance 672288009474)⟩)))
              (.cut 0 (9/136)
                (.original (.row ⟨97336292159, 99345187400, (.direct 10180561190 9574092879), (.chord .universal 10180665226 24716235638)⟩))
                (.original (.row ⟨97336292159, 99345187400, (.direct 10180561190 8981384302), (.variance 673301994573)⟩))))
            (.covered))
          (.cut 3 (-1/8)
            (.cut 3 (-3/16)
              (.original (.row ⟨95281442640, 99345187400, (.direct 19358451269 17742837469), (.chord (.midpoint ⟨485683950930, 112115482867, 197422633375, 347637871221, 197422084431, 227702871141⟩) 24716235638 43500686443)⟩))
              (.covered))
            (.covered)))
        (.cut 3 (-1/8)
          (.cut 1 (1/8)
            (.cut 2 (7/32)
              (.cut 0 (9/136)
                (.original (.row ⟨99345187399, 101311009181, (.direct 10180561190 9547454202), (.chord .universal 10180665226 24716235638)⟩))
                (.original (.row ⟨99345187399, 101311009181, (.direct 10180561190 8929377816), (.chord .universal 10180665226 24716235638)⟩)))
              (.cut 3 (-3/16)
                (.original (.row ⟨99345187399, 101311009181, (.direct 19358451269 17672236463), (.chord (.midpoint ⟨486451108388, 111669359723, 197132338247, 348001012481, 197131787673, 227702871141⟩) 24716235638 43500686443)⟩))
                (.covered)))
            (.cut 2 (7/32)
              (.cut 0 (9/136)
                (.original (.row ⟨101311009180, 103236350716, (.direct 10180561190 9520700696), (.chord .universal 10180665226 24716235638)⟩))
                (.original (.row ⟨101311009180, 103236350716, (.direct 10180561190 8877205668), (.chord .universal 10180665226 24716235638)⟩)))
              (.cut 3 (-3/16)
                (.original (.row ⟨101311009180, 103236350716, (.direct 19358451269 17601362690), (.chord (.midpoint ⟨487222818663, 111221512995, 196840184673, 348367402686, 196839632463, 227702871141⟩) 24716235638 43500686443)⟩))
                (.covered))))
          (.covered)))
      (.cut 2 (7/32)
        (.cut 3 (1/8)
          (.cut 3 (1/16)
            (.covered)
            (.cut 3 (3/32)
              (.covered)
              (.cut 2 (11/64)
                (.cut 3 (7/64)
                  (.covered)
                  (.original (.row ⟨95281442640, 103236350716, (.direct 10180561190 11239342526), (.chord (.secant 1621746870035 303462188417 92793601138 134282444165) 10180665226 16864782083)⟩)))
                (.covered))))
          (.cut 3 (3/16)
            (.cut 2 (11/64)
              (.cut 3 (5/32)
                (.cut 2 (19/128)
                  (.original (.row ⟨95281442640, 103236350716, (.direct 14500097491 15658598156), (.chord (.secant 1834375342204 422782066930 159642950444 209337960765) 10180665226 13368036905)⟩))
                  (.original (.row ⟨95281442640, 103236350716, (.direct 14500097491 15658598156), (.chord (.secant 1655870355889 321977169670 120688224722 165933692783) 13368036905 16864782083)⟩)))
                (.cut 2 (19/128)
                  (.original (.row ⟨95281442640, 103236350716, (.direct 19358451269 20596148651), (.chord (.secant 2056518657470 556095904040 240964656490 298158423466) 10180665226 13368036905)⟩))
                  (.original (.row ⟨95281442640, 103236350716, (.direct 19358451269 20596148651), (.chord (.secant 1835617174154 423504683034 184174329510 236338122957) 13368036905 16864782083)⟩))))
              (.cut 3 (5/32)
                (.covered)
                (.original (.row ⟨95281442640, 103236350716, (.direct 19358451269 20596148651), (.chord (.secant 1680851784675 335695190391 116539215032 161261863507) 16864782083 24716235638)⟩))))
            (.cut 2 (11/64)
              (.cut 3 (7/32)
                (.cut 2 (19/128)
                  (.original (.row ⟨95281442640, 103236350716, (.direct 24716051037 26015848978), (.chord (.secant 2287895889186 702427784056 334008561193 398058022940) 10180665226 13368036905)⟩))
                  (.original (.row ⟨95281442640, 103236350716, (.direct 24716051037 26015848978), (.chord (.secant 2022109625297 534946317497 257042156069 315524642703) 13368036905 16864782083)⟩)))
                (.cut 2 (19/128)
                  (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 31888945087), (.chord (.secant 2528252536980 861001347760 437804584641 508223246841) 10180665226 13368036905)⟩))
                  (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 31888945087), (.chord (.secant 2215178793382 655710822947 338499594466 402848200843) 13368036905 16864782083)⟩))))
              (.cut 3 (7/32)
                (.original (.row ⟨95281442640, 103236350716, (.direct 24716051037 26015848978), (.chord (.secant 1836520519467 424030508032 165037005890 215293719798) 16864782083 24716235638)⟩))
                (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 31888945087), (.chord (.secant 1997219707415 519755691893 219490619853 274877906944) 16864782083 24716235638)⟩))))))
        (.cut 3 (1/8)
          (.covered)
          (.cut 3 (3/16)
            (.covered)
            (.cut 2 (17/64)
              (.original (.row ⟨95281442640, 103236350716, (.direct 30541785600 31888945087), (.chord (.secant 1714975441959 354648119094 113883206743 158265229994) 24716235638 33622326476)⟩))
              (.covered))))))
    (.covered)

set_option maxRecDepth 16000 in
theorem CutMid3H0NegRestPart6_ok : CutMid3H0NegRestPart6Tree.geometryOK CutMid3H0NegPowerCache CutMid3H0NegRestPart6Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
