/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop1H1NegChartPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop1H1NegChartPart4Box : Box := ((((⟨![9/136, 4/25, 0, -1], ![9/68, 17/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop1H1NegChartPart4Tree : RatioChart :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨114055813619, 117423580140, (.direct 29705544387 31502842015), 91625974997, 274877906944, 194270549795/137438953472, .leaf (.secant 947956812746 18760293062 114172333 10180561190)⟩)
      (.cut 3 (-1/16)
        (.row ⟨114055813619, 117423580140, (.direct 9534616218 10933659387), 91625974997, 274877906944, 217552921689/137438953472, .leaf (.secant 863407657674 3082609451 4047771904 3393509060)⟩)
        (.cut 3 (-1/32)
          (.row ⟨114055813619, 117423580140, (.direct 2938560620 3939420596), 91625974997, 274877906944, 457505323071/274877906944, .leaf (.secant 822235154031 38056398 7273238970 1131165907)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 826817689 1518046096), 91625974997, 274877906944, 484504163763/274877906944, .leaf (.secant 801928511335 1349235147 11146040162 0)⟩))))
    (.cut 2 (3/4)
      (.cut 3 (1/8)
        (.cut 3 (1/16)
          (.row ⟨114055813619, 117423580140, (.direct 78125832 95708162), 91625974997, 174227471798, 251648866667/137438953472, .leaf (.midpoint ⟨781809902204, 3715297386, 37428682989, 1131177974754, 56142271612, 388320265510⟩)⟩)
          (.row ⟨114055813619, 117423580140, (.direct 1492251796 767488071), 91625974997, 174227471798, 495340658973/274877906944, .leaf (.midpoint ⟨742141834754, 10659211362, 69616913641, 728300019627, 82837299732, 380398055465⟩)⟩))
        (.row ⟨114055813619, 117423580140, (.direct 3937751229 2812031620), 91625974997, 174227471798, 255907290233/137438953472, .leaf (.midpoint ⟨703241349379, 19963510131, 93438571322, 591053288360, 104424514536, 364190815654⟩)⟩))
      (.row ⟨114055813619, 117423580140, (.direct 78125832 95708162), 174227471798, 274877906944, 2, .leaf .universal⟩))

set_option maxRecDepth 16000 in
theorem CutTop1H1NegChartPart4_ok : CutTop1H1NegChartPart4Tree.ok CutTop1H1NegChartPart4Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
