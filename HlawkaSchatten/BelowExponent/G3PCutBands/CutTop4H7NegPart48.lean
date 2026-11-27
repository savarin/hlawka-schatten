/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H7NegPart48`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H7NegPart48Box : Box := (((((((((⟨![63/136, 19/100, 0, -8], ![9/17, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).upperChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 0 (135/272)).lowerChild 3 (1/2)).upperChild 3 (3/8)

set_option maxRecDepth 16000 in
def CutTop4H7NegPart48Tree : CertTree :=
  .cut 0 (279/544)
    (.cut 3 (7/16)
      (.cut 0 (549/1088)
        (.cut 3 (13/32)
          (.cut 1 (39/200)
            (.row ⟨123862991199, 125417011706, (.direct 65931069018 74449019477), (.variance 398954912814)⟩)
            (.row ⟨125417011705, 126950446638, (.direct 65931069018 74697250804), (.variance 398569797425)⟩))
          (.row ⟨123862991199, 126950446638, (.direct 74148400816 82797225477), (.variance 387505131711)⟩))
        (.cut 3 (13/32)
          (.cut 1 (39/200)
            (.row ⟨123862991199, 125417011706, (.direct 65931069018 74591816973), (.variance 398734632035)⟩)
            (.row ⟨125417011705, 126950446638, (.direct 65931069018 74844298513), (.variance 398343844470)⟩))
          (.row ⟨123862991199, 126950446638, (.direct 74148400816 82941922981), (.variance 387315622555)⟩)))
      (.row ⟨123862991199, 126950446638, (.direct 91625662891 100038456416), (.variance 377103447228)⟩))
    (.cut 3 (7/16)
      (.cut 3 (13/32)
        (.cut 0 (567/1088)
          (.cut 1 (39/200)
            (.row ⟨123862991199, 125417011706, (.direct 65931069018 74734715432), (.variance 398514765383)⟩)
            (.row ⟨125417011705, 126950446638, (.direct 65931069018 74991452925), (.variance 398118327648)⟩))
          (.cut 1 (39/200)
            (.row ⟨123862991199, 125417011706, (.direct 65931069018 74877714805), (.variance 398295311529)⟩)
            (.row ⟨125417011705, 126950446638, (.direct 65931069018 75138713988), (.variance 397893245525)⟩)))
        (.row ⟨123862991199, 126950446638, (.direct 74148400816 83231597623), (.variance 387126429010)⟩))
      (.row ⟨123862991199, 126950446638, (.direct 91625662891 100314348286), (.variance 376776400441)⟩))

set_option maxRecDepth 16000 in
theorem CutTop4H7NegPart48_checked : CutTop4H7NegPart48Tree.commonOK CutTop4H7NegPart48Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
