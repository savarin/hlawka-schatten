/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutTop4H1NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop4H1NegChartPart7`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop4H1NegChartPart7Box : Box := (((((((((⟨![9/136, 19/100, 0, -1], ![9/68, 1/5, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 2 (5/16)).lowerChild 3 (0)).upperChild 3 (-1/8)).lowerChild 3 (-1/16)

set_option maxRecDepth 16000 in
def CutTop4H1NegChartPart7Tree : RatioChart :=
  .cut 0 (27/272)
    (.cut 3 (-3/32)
      (.row ⟨123862991199, 126950446638, (.direct 2846717485 3731184882), 43500686443, 91625974997, 365885609591/274877906944, .leaf (.secant 863407657674 3082609451 72366518 6452795533)⟩)
      (.cut 3 (-5/64)
        (.row ⟨123862991199, 126950446638, (.direct 1686607462 2442840590), 43500686443, 91625974997, 378342204811/274877906944, .leaf (.secant 842728602958 927622318 608813989 4833349683)⟩)
        (.row ⟨123862991199, 126950446638, (.direct 1194362648 1876936423), 43500686443, 91625974997, 396663334179/274877906944, .leaf (.secant 832458603362 246459794 1463531430 3393509060)⟩)))
    (.cut 3 (-3/32)
      (.row ⟨123862991199, 126950446638, (.direct 2584132506 3749557456), 43500686443, 91625974997, 47941948263/34359738368, .leaf (.secant 841517956482 831534857 1581198145 6452795533)⟩)
      (.cut 3 (-5/64)
        (.cut 0 (63/544)
          (.row ⟨123862991199, 126950446638, (.direct 1468185932 2324915886), 43500686443, 91625974997, 381887832943/274877906944, .leaf (.secant 821035462669 72364668 1521945066 4833349683)⟩)
          (.row ⟨123862991199, 126950446638, (.direct 1362672230 2332565036), 43500686443, 91625974997, 388763152169/274877906944, .leaf (.secant 810267368430 651286364 2709761451 4833349683)⟩))
        (.cut 0 (63/544)
          (.row ⟨123862991199, 126950446638, (.direct 1001754996 1769251945), 43500686443, 91625974997, 398598151253/274877906944, .leaf (.secant 810864218724 608802450 2637328759 3393509060)⟩)
          (.cut 2 (13/32)
            (.row ⟨123862991199, 126950446638, (.direct 549784721 1307280310), 43500686443, 65931360876, 50531904761/34359738368, .leaf (.secant 800145758189 1521920545 4047771904 3393509060)⟩)
            (.row ⟨123862991199, 126950446638, (.direct 909736223 1776225147), 65931360876, 91625974997, 50531904761/34359738368, .leaf (.secant 800145758189 1521920545 4047771904 3393509060)⟩)))))

set_option maxRecDepth 16000 in
theorem CutTop4H1NegChartPart7_ok : CutTop4H1NegChartPart7Tree.geometryOK CutTop4H1NegPowerCache CutTop4H1NegChartPart7Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
