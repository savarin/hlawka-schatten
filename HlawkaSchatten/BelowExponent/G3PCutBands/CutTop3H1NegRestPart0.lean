/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop3H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H1NegRestPart0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H1NegRestPart0Box : Box := (((⟨![9/136, 9/50, 0, -8], ![9/68, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).lowerChild 3 (-1/4)

set_option maxRecDepth 16000 in
def CutTop3H1NegRestPart0Tree : RatioRemainder :=
  .cut 3 (-2)
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.cut 3 (-5)
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3430927993789), (.variance 141930213726)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 797564515406), (.variance 207968996898)⟩)))
        (.cut 3 (-5)
          (.cut 3 (-13/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 5205432499188), (.variance 127252739457)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3430927993789), (.variance 141930213726)⟩)))
          (.cut 3 (-7/2)
            (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1945642005505), (.variance 164657930502)⟩))
            (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 797564515406), (.variance 207968996898)⟩)))))
      (.cut 3 (-5)
        (.cut 3 (-13/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 5340438828596 5205432499188), (.variance 127252739457)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 3523554676644 3430927993789), (.variance 141930213726)⟩)))
        (.cut 3 (-7/2)
          (.original (.row ⟨120689819474, 123862991200, (.direct 2002014560937 1945642005505), (.variance 164657930502)⟩))
          (.original (.row ⟨120689819474, 123862991200, (.direct 824633666698 797564515406), (.variance 207968996898)⟩)))))
    (.cut 2 (1/2)
      (.cut 2 (1/8)
        (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 27248237671), (.variance 503494644079)⟩))
        (.cut 3 (-9/8)
          (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 317621148721), (.variance 264669115264)⟩))
          (.cut 3 (-11/16)
            (.original (.row ⟨120689819474, 123862991200, (.direct 151782739331 143661308892), (.variance 325785589230)⟩))
            (.cut 3 (-15/32)
              (.original (.row ⟨120689819474, 123862991200, (.direct 82716570280 77082721775), (.variance 383472470323)⟩))
              (.cut 2 (5/16)
                (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 27248237671), (.variance 503494644079)⟩))
                (.cut 3 (-23/64)
                  (.original (.row ⟨120689819474, 123862991200, (.direct 54287234842 49835649261), (.chord (.midpoint ⟨392920416294, 173180432885, 225726272567, 316114218896, 231786865081, 160451927811⟩) 43500686443 91625974997)⟩))
                  (.cut 2 (13/32)
                    (.original (.row ⟨120689819474, 123862991200, (.direct 30541785600 27248237671), (.chord (.midpoint ⟨448121300585, 135102277867, 205011741034, 338457396954, 211489836056, 231598751747⟩) 43500686443 65931360876)⟩))
                    (.covered))))))))
      (.cut 3 (-9/8)
        (.original (.row ⟨120689819474, 123862991200, (.direct 331294831298 317621148721), (.variance 264669115264)⟩))
        (.cut 3 (-11/16)
          (.original (.row ⟨120689819474, 123862991200, (.direct 151782739331 143661308892), (.variance 325785589230)⟩))
          (.cut 3 (-15/32)
            (.original (.row ⟨120689819474, 123862991200, (.direct 82716570280 77082721775), (.variance 383472470323)⟩))
            (.covered)))))

set_option maxRecDepth 16000 in
theorem CutTop3H1NegRestPart0_ok : CutTop3H1NegRestPart0Tree.geometryOK CutTop3H1NegPowerCache CutTop3H1NegRestPart0Box false (1) = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
