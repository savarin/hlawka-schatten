/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H5NegPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H5NegPart6Box : Box := ((((((((((⟨![45/136, 4/25, 0, -8], ![27/68, 17/100, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).upperChild 2 (5/16)).upperChild 3 (-1/8)).lowerChild 3 (-1/16)

set_option maxRecDepth 16000 in
def CutTop1H5NegPart6Tree : CertTree :=
  .cut 3 (-3/32)
    (.cut 2 (13/32)
      (.cut 0 (99/272)
        (.row ⟨114055813619, 117423580140, (.direct 6452795533 2913730249), (.chord (.midpoint ⟨539002047393, 83240386993, 137285322003, 449851043885, 176873624661, 326150020038⟩) 43500686443 65931360876)⟩)
        (.row ⟨114055813619, 117423580140, (.direct 6452795533 2645012488), (.chord (.midpoint ⟨525207765159, 90302850024, 139449085833, 444887331186, 182270416691, 322901326891⟩) 43500686443 65931360876)⟩))
      (.row ⟨114055813619, 117423580140, (.direct 6452795533 2645012488), (.chord (.midpoint ⟨557509080406, 74201025018, 128416751171, 471678728302, 169526442509, 331152534395⟩) 65931360876 91625974997)⟩))
    (.cut 0 (99/272)
      (.cut 2 (13/32)
        (.cut 1 (33/200)
          (.row ⟨114055813619, 115752966124, (.direct 3393509060 935831295), (.chord (.midpoint ⟨579476898431, 64109847621, 117441149419, 502546581024, 160622670816, 339780828921⟩) 43500686443 65931360876)⟩)
          (.row ⟨115752966123, 117423580140, (.direct 3393509060 874978064), (.chord (.midpoint ⟨581104097794, 63389672913, 116605705851, 505098590806, 159954362291, 340255096711⟩) 43500686443 65931360876)⟩))
        (.row ⟨114055813619, 117423580140, (.direct 3393509060 874978064), (.chord (.midpoint ⟨588164123991, 60308357942, 112940696742, 516674007331, 157039533101, 346101703968⟩) 65931360876 91625974997)⟩))
      (.cut 2 (13/32)
        (.cut 1 (33/200)
          (.row ⟨114055813619, 115752966124, (.direct 3393509060 772454740), (.chord (.midpoint ⟨565025090256, 70670960066, 119997438825, 494927054973, 166503969545, 336585842183⟩) 43500686443 65931360876)⟩)
          (.row ⟨115752966123, 117423580140, (.direct 3393509060 710785838), (.chord (.midpoint ⟨566783846131, 69856591982, 119099746825, 497570942794, 165793244768, 337111014880⟩) 43500686443 65931360876)⟩))
        (.row ⟨114055813619, 117423580140, (.direct 3393509060 710785838), (.chord (.midpoint ⟨572918000805, 67050773816, 115938620996, 507158871491, 163303697492, 342629067500⟩) 65931360876 91625974997)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop1H5NegPart6_checked : CutTop1H5NegPart6Tree.commonOK CutTop1H5NegPart6Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
