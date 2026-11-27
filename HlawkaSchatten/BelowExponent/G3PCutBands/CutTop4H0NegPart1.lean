/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H0NegPart1`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H0NegPart1Box : Box := ((((((⟨![0, 19/100, 0, -8], ![9/136, 1/5, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).lowerChild 2 (1/8)

set_option maxRecDepth 16000 in
def CutTop4H0NegPart1Tree : CertTree :=
  .cut 3 (0)
    (.row ⟨123862991199, 126950446638, (.direct 0 114172333), (.chord .universal 0 10180665226)⟩)
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.cut 1 (39/200)
          (.row ⟨123862991199, 125417011706, (.direct 3393509060 3988189359), (.chord .universal 0 10180665226)⟩)
          (.row ⟨125417011705, 126950446638, (.direct 3393509060 4005645522), (.chord .universal 0 10180665226)⟩))
        (.cut 3 (3/32)
          (.cut 2 (1/16)
            (.row ⟨123862991199, 126950446638, (.direct 6452795533 7194797152), (.variance 868750156237)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 6452795533 7194797152), (.chord (.secant 2099545511225 582778416214 73163544754 91625662891) 3393555298 10180665226)⟩))
          (.cut 3 (7/64)
            (.cut 2 (1/16)
              (.row ⟨123862991199, 126950446638, (.direct 8238656156 9034166424), (.variance 734193276773)⟩)
              (.row ⟨123862991199, 126950446638, (.direct 8238656156 9034166424), (.chord (.secant 2333081667631 731767288146 150498559827 174227225485) 3393555298 10180665226)⟩))
            (.cut 1 (39/200)
              (.row ⟨123862991199, 125417011706, (.direct 10180561190 10999926272), (.variance 688691889909)⟩)
              (.row ⟨125417011705, 126950446638, (.direct 10180561190 11023608647), (.variance 688691889909)⟩)))))
      (.cut 3 (3/16)
        (.cut 3 (5/32)
          (.cut 3 (9/64)
            (.row ⟨123862991199, 126950446638, (.direct 12270063068 13155474884), (.variance 651562574406)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 14500097491 15423303066), (.variance 620477318811)⟩))
          (.cut 3 (11/64)
            (.row ⟨123862991199, 126950446638, (.direct 16864636136 17821534138), (.variance 593929411221)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 19358451269 20345315715), (.variance 570893780246)⟩)))
        (.cut 3 (7/32)
          (.row ⟨123862991199, 126950446638, (.direct 24716051037 25752845602), (.variance 550644921433)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 30541785600 31616683754), (.variance 516518883525)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop4H0NegPart1_checked : CutTop4H0NegPart1Tree.commonOK CutTop4H0NegPart1Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
