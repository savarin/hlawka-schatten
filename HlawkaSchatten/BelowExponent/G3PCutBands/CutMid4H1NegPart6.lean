/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid4H1NegPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid4H1NegPart6Box : Box := ((((((((⟨![9/68, 13/100, 0, -8], ![9/34, 3/20, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)).upperChild 3 (0)).upperChild 3 (1/8)

set_option maxRecDepth 16000 in
def CutMid4H1NegPart6Tree : CertTree :=
  .cut 3 (3/16)
    (.cut 1 (7/50)
      (.cut 3 (5/32)
        (.cut 0 (27/136)
          (.cut 1 (27/200)
            (.row ⟨103236350715, 105123556200, (.direct 14500097491 16323763057), (.variance 634900105205)⟩)
            (.row ⟨105123556199, 106974752992, (.direct 14500097491 16398025912), (.variance 634243611941)⟩))
          (.row ⟨103236350715, 106974752992, (.direct 14500097491 17049594500), (.variance 627094320551)⟩))
        (.cut 0 (27/136)
          (.row ⟨103236350715, 106974752992, (.direct 19358451269 21382714036), (.variance 582095824638)⟩)
          (.row ⟨103236350715, 106974752992, (.direct 19358451269 22073802796), (.variance 576472071599)⟩)))
      (.cut 3 (5/32)
        (.cut 0 (27/136)
          (.cut 1 (29/200)
            (.row ⟨106974752991, 108791878640, (.direct 14500097491 16472814447), (.variance 633585916404)⟩)
            (.row ⟨108791878639, 110576703735, (.direct 14500097491 16548133791), (.variance 632927013583)⟩))
          (.cut 1 (29/200)
            (.row ⟨106974752991, 108791878640, (.direct 14500097491 17150782510), (.variance 625207483161)⟩)
            (.row ⟨108791878639, 110576703735, (.direct 14500097491 17252740090), (.variance 624263740862)⟩)))
        (.cut 0 (27/136)
          (.cut 1 (29/200)
            (.row ⟨106974752991, 108791878640, (.direct 19358451269 21462132255), (.variance 581152579294)⟩)
            (.row ⟨108791878639, 110576703735, (.direct 19358451269 21542089254), (.variance 580679113641)⟩))
          (.row ⟨106974752991, 110576703735, (.direct 19358451269 22288902822), (.variance 575105023688)⟩))))
    (.cut 1 (7/50)
      (.cut 3 (7/32)
        (.cut 0 (27/136)
          (.row ⟨103236350715, 106974752992, (.direct 24716051037 26839291618), (.variance 541781930204)⟩)
          (.row ⟨103236350715, 106974752992, (.direct 24716051037 27561238827), (.variance 537528693760)⟩))
        (.row ⟨103236350715, 106974752992, (.direct 30541785600 33485620126), (.variance 509633938482)⟩))
      (.cut 3 (7/32)
        (.cut 0 (27/136)
          (.row ⟨106974752991, 110576703735, (.direct 24716051037 27005908265), (.variance 541070404616)⟩)
          (.row ⟨106974752991, 110576703735, (.direct 24716051037 27785661072), (.variance 536490798150)⟩))
        (.cut 0 (27/136)
          (.row ⟨106974752991, 110576703735, (.direct 30541785600 32912457841), (.variance 509078357485)⟩)
          (.row ⟨106974752991, 110576703735, (.direct 30541785600 33717064942), (.variance 505492345708)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid4H1NegPart6_checked : CutMid4H1NegPart6Tree.commonOK CutMid4H1NegPart6Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
