/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H2NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H2NegPart2Box : Box := (((((((((⟨![9/68, 4/25, 0, -8], ![27/136, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop1H2NegPart2Tree : CertTree :=
  .cut 2 (7/32)
    (.cut 3 (-3/16)
      (.row ⟨114055813619, 117423580140, (.direct 19358451269 15899272963), (.variance 579775454516)⟩)
      (.row ⟨114055813619, 117423580140, (.direct 10180561190 7635559061), (.chord (.midpoint ⟨463811424548, 125224810498, 192262292236, 354232552895, 205646037986, 163353989593⟩) 10180665226 24716235638)⟩))
    (.cut 3 (-3/16)
      (.row ⟨114055813619, 117423580140, (.direct 19358451269 15899272963), (.chord (.midpoint ⟨435942513717, 143049815439, 203098925418, 340715984240, 215998920477, 227627324213⟩) 24716235638 43500686443)⟩)
      (.cut 0 (45/272)
        (.row ⟨114055813619, 117423580140, (.direct 10180561190 8040855907), (.chord (.midpoint ⟨535428987311, 85042917744, 163364699871, 397627493877, 178277668572, 281240325335⟩) 24716235638 43500686443)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 10180561190 7635559061), (.chord (.midpoint ⟨523209448002, 91349233808, 164635489259, 395447404747, 183047086707, 278466961066⟩) 24716235638 43500686443)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop1H2NegPart2_checked : CutTop1H2NegPart2Tree.commonOK CutTop1H2NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
