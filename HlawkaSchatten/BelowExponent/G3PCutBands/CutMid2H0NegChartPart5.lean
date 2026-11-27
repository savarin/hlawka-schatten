/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCutBands.CutMid2H0NegPower

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutMid2H0NegChartPart5`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutMid2H0NegChartPart5Box : Box := ((((((⟨![0, 9/100, 0, -1], ![9/68, 11/100, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).lowerChild 2 (1/2)).upperChild 2 (1/8)).upperChild 2 (5/16)

set_option maxRecDepth 16000 in
def CutMid2H0NegChartPart5Tree : RatioChart :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨86531900008, 95281442641, (.direct 10180561190 11064363690), 43500686443, 91625974997, 25351008853/17179869184, .leaf (.secant 993888389401 30541785600 114172333 10180561190)⟩)
      (.cut 0 (9/136)
        (.row ⟨86531900008, 95281442641, (.direct 3393509060 3709506711), 43500686443, 91625974997, 126238934899/68719476736, .leaf (.secant 907805998772 10180561190 3715346965 0)⟩)
        (.cut 3 (-1/16)
          (.row ⟨86531900008, 95281442641, (.direct 3144629907 3772032159), 43500686443, 91625974997, 217552921689/137438953472, .leaf (.secant 863407657674 3082609451 4047771904 3393509060)⟩)
          (.row ⟨86531900008, 95281442641, (.direct 962314059 1397263040), 43500686443, 91625974997, 495313074485/274877906944, .leaf (.secant 822235154031 38056398 11146040162 0)⟩))))
    (.cut 1 (1/10)
      (.cut 0 (9/136)
        (.row ⟨86531900008, 91020629598, (.direct 0 34931964), 43500686443, 91625974997, 2, .leaf .universal⟩)
        (.row ⟨86531900008, 91020629598, (.direct 29459353 41107490), 43500686443, 91625974997, 2, .leaf .universal⟩))
      (.cut 0 (9/136)
        (.cut 1 (21/200)
          (.row ⟨91020629597, 93177423805, (.direct 0 37898415), 43500686443, 91625974997, 2, .leaf .universal⟩)
          (.cut 0 (9/272)
            (.row ⟨93177423804, 95281442641, (.direct 0 13656520), 43500686443, 91625974997, 2, .leaf .universal⟩)
            (.row ⟨93177423804, 95281442641, (.direct 12669209 14752221), 43500686443, 91625974997, 2, .leaf .universal⟩)))
        (.cut 3 (1/8)
          (.cut 3 (1/16)
            (.row ⟨91020629597, 95281442641, (.direct 35124696 47617742), 43500686443, 91625974997, 251648866667/137438953472, .leaf (.midpoint ⟨781809902204, 3715297386, 37428682989, 1131177974754, 56142271612, 388320265510⟩)⟩)
            (.row ⟨91020629597, 95281442641, (.direct 700421008 361451019), 43500686443, 91625974997, 495340658973/274877906944, .leaf (.midpoint ⟨742141834754, 10659211362, 69616913641, 728300019627, 82837299732, 380398055465⟩)⟩))
          (.row ⟨91020629597, 95281442641, (.direct 1854893001 1333113169), 43500686443, 91625974997, 255907290233/137438953472, .leaf (.midpoint ⟨703241349379, 19963510131, 93438571322, 591053288360, 104424514536, 364190815654⟩)⟩))))

set_option maxRecDepth 16000 in
theorem CutMid2H0NegChartPart5_ok : CutMid2H0NegChartPart5Tree.geometryOK CutMid2H0NegPowerCache CutMid2H0NegChartPart5Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
