/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H1NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H1NegPart2Box : Box := (((((((((⟨![9/136, 9/50, 0, -8], ![9/68, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop3H1NegPart2Tree : CertTree :=
  .cut 1 (37/200)
    (.cut 3 (-3/16)
      (.cut 2 (7/32)
        (.row ⟨120689819474, 122287555846, (.direct 19358451269 16803394016), (.variance 571439193894)⟩)
        (.row ⟨120689819474, 122287555846, (.direct 19358451269 16803394016), (.chord (.midpoint ⟨460655851866, 127179128475, 200240488067, 344159744282, 206824759184, 234504142539⟩) 24716235638 43500686443)⟩))
      (.cut 2 (7/32)
        (.row ⟨120689819474, 122287555846, (.direct 10180561190 8292315504), (.chord (.midpoint ⟨485507733435, 112218087635, 190678642343, 356317440911, 197488747245, 167736188034⟩) 10180665226 24716235638)⟩)
        (.cut 0 (27/272)
          (.row ⟨120689819474, 122287555846, (.direct 10180561190 8750951301), (.chord (.midpoint ⟨562008749199, 72077930597, 160041330856, 403468424444, 167719800043, 287398746484⟩) 24716235638 43500686443)⟩)
          (.row ⟨120689819474, 122287555846, (.direct 10180561190 8292315504), (.chord (.midpoint ⟨550172578466, 77725073909, 161078036285, 401624279745, 172454570935, 285004411288⟩) 24716235638 43500686443)⟩))))
    (.cut 3 (-3/16)
      (.cut 2 (7/32)
        (.row ⟨122287555845, 123862991200, (.direct 19358451269 16729150279), (.variance 572102195128)⟩)
        (.row ⟨122287555845, 123862991200, (.direct 19358451269 16729150279), (.chord (.midpoint ⟨461463127861, 126677631461, 199932107225, 344536298187, 206523384069, 234710111328⟩) 24716235638 43500686443)⟩))
      (.cut 2 (7/32)
        (.row ⟨122287555845, 123862991200, (.direct 10180561190 8238139508), (.chord (.midpoint ⟨486621792855, 111570226600, 190246429831, 356891602574, 197067181446, 168170246918⟩) 10180665226 24716235638)⟩)
        (.cut 0 (27/272)
          (.row ⟨122287555845, 123862991200, (.direct 10180561190 8709490155), (.chord (.midpoint ⟨562625948311, 71788979031, 159784452765, 403928532914, 167471333192, 287568138374⟩) 24716235638 43500686443)⟩)
          (.row ⟨122287555845, 123862991200, (.direct 10180561190 8238139508), (.chord (.midpoint ⟨550989129212, 77329008633, 160737035672, 402228624735, 172129714750, 285259983952⟩) 24716235638 43500686443)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop3H1NegPart2_checked : CutTop3H1NegPart2Tree.commonOK CutTop3H1NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
