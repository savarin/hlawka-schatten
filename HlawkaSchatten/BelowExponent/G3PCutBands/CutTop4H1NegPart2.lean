/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H1NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H1NegPart2Box : Box := (((((((((⟨![9/136, 19/100, 0, -8], ![9/68, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop4H1NegPart2Tree : CertTree :=
  .cut 1 (39/200)
    (.cut 3 (-3/16)
      (.cut 2 (7/32)
        (.row ⟨123862991199, 125417011706, (.direct 19358451269 16654617638), (.variance 572771521423)⟩)
        (.row ⟨123862991199, 125417011706, (.direct 19358451269 16654617638), (.chord (.midpoint ⟨462275402196, 126174093832, 199621677235, 344916358391, 206220024329, 234917088844⟩) 24716235638 43500686443)⟩))
      (.cut 2 (7/32)
        (.row ⟨123862991199, 125417011706, (.direct 10180561190 8183795634), (.chord (.midpoint ⟨487742974307, 110920173320, 189811119160, 357472138269, 196642633954, 168605903916⟩) 10180665226 24716235638)⟩)
        (.cut 0 (27/272)
          (.row ⟨123862991199, 125417011706, (.direct 10180561190 8667872630), (.chord (.midpoint ⟨563246818878, 71498858803, 159525855739, 404392999270, 167221225791, 287738394778⟩) 24716235638 43500686443)⟩)
          (.row ⟨123862991199, 125417011706, (.direct 10180561190 8183795634), (.chord (.midpoint ⟨551810654365, 76931502592, 160393627520, 402839455631, 171802619606, 285516804915⟩) 24716235638 43500686443)⟩))))
    (.cut 3 (-3/16)
      (.cut 2 (7/32)
        (.row ⟨125417011705, 126950446638, (.direct 19358451269 16579794853), (.variance 573447265958)⟩)
        (.row ⟨125417011705, 126950446638, (.direct 19358451269 16579794853), (.chord (.midpoint ⟨463092720671, 125668505527, 199309176874, 345299975221, 205914659659, 235125082669⟩) 24716235638 43500686443)⟩))
      (.cut 2 (7/32)
        (.row ⟨125417011705, 126950446638, (.direct 10180561190 8129283818), (.chord (.midpoint ⟨488871344500, 110267923362, 189372674678, 358059158477, 196215071104, 169043170688⟩) 10180665226 24716235638)⟩)
        (.cut 0 (27/272)
          (.row ⟨125417011705, 126950446638, (.direct 10180561190 8626098130), (.chord (.midpoint ⟨563871393527, 71207564248, 159265521809, 404861887216, 166969460995, 287909522388⟩) 24716235638 43500686443)⟩)
          (.row ⟨125417011705, 126950446638, (.direct 10180561190 8129283818), (.chord (.midpoint ⟨552637198968, 76532551105, 160047784716, 403456880840, 171473261127, 285774883547⟩) 24716235638 43500686443)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop4H1NegPart2_checked : CutTop4H1NegPart2Tree.commonOK CutTop4H1NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
