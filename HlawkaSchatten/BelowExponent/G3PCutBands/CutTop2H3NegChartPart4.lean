/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop2H3NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop2H3NegChartPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop2H3NegChartPart4Box : Box := ((((((((⟨![27/136, 17/100, 0, -1], ![9/34, 9/50, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 2 (5/16)).lowerChild 3 (0)).lowerChild 3 (-1/8)

set_option maxRecDepth 16000 in
def CutTop2H3NegChartPart4Tree : RatioChart :=
  .cut 3 (-3/16)
    (.cut 0 (63/272)
      (.row ⟨117423580139, 120689819475, (.direct 8141508118 10699190401), 43500686443, 91625974997, 352871896151/274877906944, .leaf (.secant 858525362214 2494612905 1953895586 19358451269)⟩)
      (.row ⟨117423580139, 120689819475, (.direct 7811163956 10724205521), 43500686443, 91625974997, 90721324789/68719476736, .leaf (.secant 836681797691 487834261 4743594121 19358451269)⟩))
    (.cut 0 (63/272)
      (.cut 3 (-5/32)
        (.row ⟨117423580139, 120689819475, (.direct 4696532978 6908313129), 43500686443, 91625974997, 365720802777/274877906944, .leaf (.secant 817440269340 217094729 4565834898 14500097491)⟩)
        (.row ⟨117423580139, 120689819475, (.direct 3248697638 5250989457), 43500686443, 91625974997, 193940594035/137438953472, .leaf (.secant 797177758400 1826413451 7911985758 10180561190)⟩))
      (.cut 3 (-5/32)
        (.row ⟨117423580139, 120689819475, (.direct 4418259593 6930362453), 43500686443, 91625974997, 372951398187/274877906944, .leaf (.secant 795991698633 1953865619 8129283818 14500097491)⟩)
        (.cut 0 (135/544)
          (.row ⟨117423580139, 120689819475, (.direct 3002421114 5116037580), 43500686443, 91625974997, 192364880923/137438953472, .leaf (.secant 775928631105 4565776888 9944394259 10180561190)⟩)
          (.row ⟨117423580139, 120689819475, (.direct 2881424321 5125877698), 43500686443, 91625974997, 193489998641/137438953472, .leaf (.secant 765383709890 6253410130 12143314914 10180561190)⟩))))

set_option maxRecDepth 16000 in
theorem CutTop2H3NegChartPart4_ok : CutTop2H3NegChartPart4Tree.geometryOK CutTop2H3NegPowerCache CutTop2H3NegChartPart4Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
