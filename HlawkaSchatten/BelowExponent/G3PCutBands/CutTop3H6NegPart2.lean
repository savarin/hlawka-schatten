/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop3H6NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop3H6NegPart2Box : Box := ((((((((⟨![27/68, 9/50, 0, -8], ![63/136, 19/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop3H6NegPart2Tree : CertTree :=
  .cut 2 (5/16)
    (.cut 2 (7/32)
      (.cut 3 (-3/16)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 10801343318), (.variance 641543215824)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 4088422227), (.chord (.midpoint ⟨407305920451, 162738774758, 187478832219, 360621700330, 226527536604, 163125883833⟩) 10180665226 24716235638)⟩))
      (.cut 3 (-3/16)
        (.row ⟨120689819474, 123862991200, (.direct 19358451269 10801343318), (.chord (.midpoint ⟨361044873578, 197707665279, 206595881177, 336613993319, 243399444286, 207491484692⟩) 24716235638 43500686443)⟩)
        (.row ⟨120689819474, 123862991200, (.direct 10180561190 4088422227), (.chord (.midpoint ⟨456924368629, 129510950808, 166282535000, 392664269828, 208216309962, 257236432485⟩) 24716235638 43500686443)⟩)))
    (.cut 3 (-3/16)
      (.row ⟨120689819474, 123862991200, (.direct 19358451269 10801343318), (.chord (.midpoint ⟨438890854586, 141102970532, 174093018054, 380082148306, 214909284678, 257412263296⟩) 43500686443 91625974997)⟩)
      (.cut 0 (117/272)
        (.cut 2 (13/32)
          (.row ⟨120689819474, 123862991200, (.direct 10180561190 4454442234), (.chord (.midpoint ⟨479349414404, 115834327353, 156357034230, 410190946210, 199814089804, 293576397361⟩) 43500686443 65931360876)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 10180561190 4454442234), (.chord (.midpoint ⟨497797983567, 105177255096, 147979468978, 426535045841, 192821867038, 309244722841⟩) 65931360876 91625974997)⟩))
        (.cut 2 (13/32)
          (.row ⟨120689819474, 123862991200, (.direct 10180561190 4088422227), (.chord (.midpoint ⟨466855610290, 123354689590, 158012595762, 407136991716, 204507181838, 290394807067⟩) 43500686443 65931360876)⟩)
          (.row ⟨120689819474, 123862991200, (.direct 10180561190 4088422227), (.chord (.midpoint ⟨484158722344, 113005169706, 150146196031, 422158624955, 197998843888, 305751727999⟩) 65931360876 91625974997)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop3H6NegPart2_checked : CutTop3H6NegPart2Tree.commonOK CutTop3H6NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
