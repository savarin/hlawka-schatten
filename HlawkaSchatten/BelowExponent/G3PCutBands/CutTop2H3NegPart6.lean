/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H3NegPart6`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H3NegPart6Box : Box := (((((((((⟨![27/136, 17/100, 0, -8], ![9/34, 9/50, 1, 8]⟩ : Box)).lowerChild 3 (3/4)).upperChild 3 (-1/4)).lowerChild 3 (1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).lowerChild 3 (0)).upperChild 2 (5/16)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop2H3NegPart6Tree : CertTree :=
  .cut 2 (13/32)
    (.cut 3 (-3/16)
      (.row ⟨117423580139, 120689819475, (.direct 19358451269 14524006646), (.chord (.midpoint ⟨477301143586, 117050287225, 179858942361, 371396152430, 200585680471, 276332704819⟩) 43500686443 65931360876)⟩)
      (.cut 0 (63/272)
        (.cut 1 (7/40)
          (.row ⟨117423580139, 119068833411, (.direct 10180561190 7149452018), (.chord (.midpoint ⟨553542984329, 76096484015, 147609555888, 427293172019, 171112020018, 311510859003⟩) 43500686443 65931360876)⟩)
          (.row ⟨119068833410, 120689819475, (.direct 10180561190 7060772586), (.chord (.midpoint ⟨554632708369, 75573431714, 147126324344, 428288447687, 170676992681, 311843095906⟩) 43500686443 65931360876)⟩))
        (.cut 1 (7/40)
          (.row ⟨117423580139, 119068833411, (.direct 10180561190 6749274439), (.chord (.midpoint ⟨539896875733, 82791887484, 149539674193, 423372767526, 176521300871, 308349602452⟩) 43500686443 65931360876)⟩)
          (.row ⟨119068833410, 120689819475, (.direct 10180561190 6650100644), (.chord (.midpoint ⟨541130926173, 82175281958, 148992401507, 424475552039, 176034948154, 308739999861⟩) 43500686443 65931360876)⟩))))
    (.cut 3 (-3/16)
      (.row ⟨117423580139, 120689819475, (.direct 19358451269 14524006646), (.chord (.midpoint ⟨516427370477, 94944829931, 163652779722, 397130745459, 185673890374, 302320190230⟩) 65931360876 91625974997)⟩)
      (.cut 0 (63/272)
        (.cut 1 (7/40)
          (.row ⟨117423580139, 119068833411, (.direct 10180561190 7149452018), (.chord (.midpoint ⟨579807472944, 63963236764, 135729895077, 453502637102, 160487004164, 329151406185⟩) 65931360876 91625974997)⟩)
          (.row ⟨119068833410, 120689819475, (.direct 10180561190 7060772586), (.chord (.midpoint ⟨580708083405, 63564598048, 135313216613, 454493026779, 160117128192, 329397205377⟩) 65931360876 91625974997)⟩))
        (.row ⟨117423580139, 120689819475, (.direct 10180561190 6650100644), (.chord (.midpoint ⟨566006901827, 70215800814, 137738712655, 448799923074, 166107378549, 325728232259⟩) 65931360876 91625974997)⟩)))

set_option maxRecDepth 16000 in
theorem CutTop2H3NegPart6_checked : CutTop2H3NegPart6Tree.commonOK CutTop2H3NegPart6Box false = true := by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
