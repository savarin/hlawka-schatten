/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H1NegPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H1NegPart2Box : Box := (((((((((⟨![9/136, 4/25, 0, -8], ![9/68, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop1H1NegPart2Tree : CertTree :=
  .cut 1 (33/200)
    (.cut 3 (-3/16)
      (.cut 2 (7/32)
        (.row ⟨114055813619, 115752966124, (.direct 19358451269 17097504751), (.variance 568848639147)⟩)
        (.row ⟨114055813619, 115752966124, (.direct 19358451269 17097504751), (.chord (.midpoint ⟨457475834164, 129164910748, 201453933956, 342687618274, 208010809707, 233690205612⟩) 24716235638 43500686443)⟩))
      (.cut 2 (7/32)
        (.row ⟨114055813619, 115752966124, (.direct 10180561190 8507342535), (.chord (.midpoint ⟨481121409902, 114787702596, 192377203895, 354082412994, 199145848419, 166015704299⟩) 10180665226 24716235638)⟩)
        (.row ⟨114055813619, 115752966124, (.direct 10180561190 8507342535), (.chord (.midpoint ⟨565654451358, 70379035331, 158521231158, 406209688393, 166249794667, 281532839484⟩) 24716235638 43500686443)⟩)))
    (.cut 3 (-3/16)
      (.cut 2 (7/32)
        (.row ⟨115752966123, 117423580140, (.direct 19358451269 17024404214), (.variance 569487235977)⟩)
        (.row ⟨115752966123, 117423580140, (.direct 19358451269 17024404214), (.chord (.midpoint ⟨458263564028, 128671476075, 201153543430, 343050631368, 207717175622, 233892213825⟩) 24716235638 43500686443)⟩))
      (.cut 2 (7/32)
        (.row ⟨115752966123, 117423580140, (.direct 10180561190 8453837094), (.chord (.midpoint ⟨482207632314, 114148563588, 191957038859, 354632133253, 198735883217, 166443485121⟩) 10180665226 24716235638)⟩)
        (.cut 0 (27/272)
          (.row ⟨115752966123, 117423580140, (.direct 10180561190 8874402476), (.chord (.midpoint ⟨560178859971, 72937829777, 160801827396, 402113627755, 168455522224, 286895691996⟩) 24716235638 43500686443)⟩)
          (.row ⟨115752966123, 117423580140, (.direct 10180561190 8453837094), (.chord (.midpoint ⟨547752330203, 78904672605, 162086857672, 399849112014, 173415944031, 284245090804⟩) 24716235638 43500686443)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop1H1NegPart2_checked : CutTop1H1NegPart2Tree.commonOK CutTop1H1NegPart2Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
