/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H3NegChartPart4`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H3NegChartPart4Box : Box := ((((⟨![27/136, 3/20, 0, -1], ![9/34, 4/25, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop0H3NegChartPart4Tree : RatioChart :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨110576703734, 114055813620, (.direct 28200228675 31569806171), 91625974997, 274877906944, 435430222057/274877906944, .leaf (.secant 858525362214 2494612905 12143314914 10180561190)⟩)
      (.cut 3 (-1/16)
        (.row ⟨110576703734, 114055813620, (.direct 8395565827 10986551039), 91625974997, 274877906944, 113991657799/68719476736, .leaf (.secant 777103573830 4390537685 21819715475 3393509060)⟩)
        (.cut 3 (-1/32)
          (.row ⟨110576703734, 114055813620, (.direct 2171848894 3978336860), 91625974997, 274877906944, 462184348107/274877906944, .leaf (.secant 737525261110 11640621485 27401114573 1131165907)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 368519893 1546374280), 91625974997, 274877906944, 477255881667/274877906944, .leaf (.secant 718023746068 16155543155 33438118291 0)⟩))))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.row ⟨110576703734, 114055813620, (.direct 405563324 106426897), 91625974997, 274877906944, 469428183417/274877906944, .leaf (.midpoint ⟨698715786042, 21194109732, 71170913946, 716981059011, 106755515687, 371402902422⟩)⟩)
        (.row ⟨110576703734, 114055813620, (.direct 2242289942 744254886), 91625974997, 274877906944, 473821297551/274877906944, .leaf (.midpoint ⟨660686111899, 32704812791, 94703620722, 585440564463, 125291677173, 363221546020⟩)⟩))
      (.row ⟨110576703734, 114055813620, (.direct 5006850197 2773256522), 91625974997, 274877906944, 60163676541/34359738368, .leaf (.midpoint ⟨623447754071, 45958852171, 114646126856, 511208959093, 142054633983, 346452473114⟩)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H3NegChartPart4_ok : CutTop0H3NegChartPart4Tree.ok CutTop0H3NegChartPart4Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
