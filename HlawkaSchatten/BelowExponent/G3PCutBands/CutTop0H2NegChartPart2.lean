/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData

/-! Certificate data for the ordered G3 vertex corner: cut band piece `CutTop0H2NegChartPart2`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

def CutTop0H2NegChartPart2Box : Box := ((((⟨![9/68, 3/20, 0, -1], ![27/136, 4/25, 1, 1]⟩ : Box)).lowerChild 3 (1/4)).upperChild 3 (-1/4)).upperChild 2 (1/2)

set_option maxRecDepth 16000 in
def CutTop0H2NegChartPart2Tree : RatioChart :=
  .cut 3 (0)
    (.cut 3 (-1/8)
      (.row ⟨110576703734, 114055813620, (.direct 28981506533 31506441603), 91625974997, 274877906944, 13050873865/8589934592, .leaf (.secant 902832344944 9247859247 4390594002 10180561190)⟩)
      (.cut 3 (-1/16)
        (.row ⟨110576703734, 114055813620, (.direct 8982805544 10936501179), 91625974997, 274877906944, 451402709729/274877906944, .leaf (.secant 819836417934 114169576 11640735603 3393509060)⟩)
        (.cut 3 (-1/32)
          (.row ⟨110576703734, 114055813620, (.direct 2560972707 3941509681), 91625974997, 274877906944, 463382913763/274877906944, .leaf (.secant 779455427041 4047718964 16155685117 1131165907)⟩)
          (.row ⟨110576703734, 114055813620, (.direct 590715792 1519564491), 91625974997, 274877906944, 482894015325/274877906944, .leaf (.secant 759548459881 7273157061 21194278130 0)⟩))))
    (.cut 3 (1/8)
      (.cut 3 (1/16)
        (.row ⟨110576703734, 114055813620, (.direct 211454116 96273824), 91625974997, 274877906944, 240592859799/137438953472, .leaf (.midpoint ⟨739832218923, 11145929393, 56143020797, 848383425373, 84213688747, 379928401292⟩)⟩)
        (.row ⟨110576703734, 114055813620, (.direct 1837195924 766232035), 91625974997, 274877906944, 485151939901/274877906944, .leaf (.midpoint ⟨700977219794, 20575414255, 82838134442, 643770644805, 105594578819, 371880172203⟩)⟩))
      (.row ⟨110576703734, 114055813620, (.direct 4437600526 2809941480), 91625974997, 274877906944, 248381045105/137438953472, .leaf (.midpoint ⟨662901361859, 31977740914, 104425363607, 546224978863, 124256364695, 355400176683⟩)⟩))

set_option maxRecDepth 16000 in
theorem CutTop0H2NegChartPart2_ok : CutTop0H2NegChartPart2Tree.ok CutTop0H2NegChartPart2Box false = true :=
  by decide +kernel

end HlawkaSchatten.BelowExponent.G3P
