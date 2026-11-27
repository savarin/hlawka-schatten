/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7NegPart2Box : Box := ((((((((⟨![63/136, 19/100, 0, -8], ![9/17, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop4H7NegPart2Tree : CertTree :=
  .cut 2 (5/16)
    (.cut 2 (7/32)
      (.cut 3 (-3/16)
        (.row ⟨123862991199, 126950446638, (.direct 19358451269 9247956506), (.variance 668164857530)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 3082652371), (.chord (.midpoint ⟨400408166787, 167698296225, 183364525777, 366344236179, 229051331429, 168356301506⟩) 10180665226 24716235638)⟩))
      (.cut 3 (-3/16)
        (.row ⟨123862991199, 126950446638, (.direct 19358451269 9247956506), (.chord (.midpoint ⟨347919001775, 208393380471, 205479461302, 337910601416, 248174253451, 204986531454⟩) 24716235638 43500686443)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 10180561190 3082652371), (.chord (.midpoint ⟨441534213599, 139369966780, 165449655207, 394065728689, 213931325983, 254635003748⟩) 24716235638 43500686443)⟩)))
    (.cut 3 (-3/16)
      (.row ⟨123862991199, 126950446638, (.direct 19358451269 9247956506), (.chord (.midpoint ⟨417363583850, 155660231445, 176057543494, 377068124648, 222839910280, 252536683302⟩) 43500686443 91625974997)⟩)
      (.cut 0 (135/272)
        (.cut 2 (13/32)
          (.row ⟨123862991199, 126950446638, (.direct 10180561190 3433189219), (.chord (.midpoint ⟨458917435091, 128262657617, 157652282538, 407796979556, 207473356511, 288850717780⟩) 43500686443 65931360876)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 10180561190 3433189219), (.chord (.midpoint ⟨474307435714, 118839419500, 150608415914, 421238962762, 201711838403, 303464231928⟩) 65931360876 91625974997)⟩))
        (.cut 2 (13/32)
          (.row ⟨123862991199, 126950446638, (.direct 10180561190 3082652371), (.chord (.midpoint ⟨446917728680, 135876664574, 159165034532, 405043225696, 211936429613, 285751362230⟩) 43500686443 65931360876)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 10180561190 3082652371), (.chord (.midpoint ⟨461152459597, 126870500278, 152637044288, 417259055740, 206639377698, 300012434245⟩) 65931360876 91625974997)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop4H7NegPart2_checked : CutTop4H7NegPart2Tree.commonOK CutTop4H7NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
