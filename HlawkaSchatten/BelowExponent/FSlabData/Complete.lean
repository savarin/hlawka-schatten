/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabData.Slabs0
public import HlawkaSchatten.BelowExponent.FSlabData.Slabs39
public import HlawkaSchatten.BelowExponent.FSlabData.Slabs78
public import HlawkaSchatten.BelowExponent.FSlabData.Slabs117

/-!
# Balanced certificates for the facet strip

Each of the 156 slabs has a fixed weight and a checked row bound. The finite case split
combines these certificates into `SlabChecked i` for every index. The schedule places an
ordered profile in this family or in the adjoining balanced-edge region.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true

public section

namespace HlawkaSchatten.BelowExponent

open FSlabCheck

private theorem allChecked (i : Fin 156) : SlabChecked i := by
  fin_cases i
  · exact slab0_ok
  · exact slab1_ok
  · exact slab2_ok
  · exact slab3_ok
  · exact slab4_ok
  · exact slab5_ok
  · exact slab6_ok
  · exact slab7_ok
  · exact slab8_ok
  · exact slab9_ok
  · exact slab10_ok
  · exact slab11_ok
  · exact slab12_ok
  · exact slab13_ok
  · exact slab14_ok
  · exact slab15_ok
  · exact slab16_ok
  · exact slab17_ok
  · exact slab18_ok
  · exact slab19_ok
  · exact slab20_ok
  · exact slab21_ok
  · exact slab22_ok
  · exact slab23_ok
  · exact slab24_ok
  · exact slab25_ok
  · exact slab26_ok
  · exact slab27_ok
  · exact slab28_ok
  · exact slab29_ok
  · exact slab30_ok
  · exact slab31_ok
  · exact slab32_ok
  · exact slab33_ok
  · exact slab34_ok
  · exact slab35_ok
  · exact slab36_ok
  · exact slab37_ok
  · exact slab38_ok
  · exact slab39_ok
  · exact slab40_ok
  · exact slab41_ok
  · exact slab42_ok
  · exact slab43_ok
  · exact slab44_ok
  · exact slab45_ok
  · exact slab46_ok
  · exact slab47_ok
  · exact slab48_ok
  · exact slab49_ok
  · exact slab50_ok
  · exact slab51_ok
  · exact slab52_ok
  · exact slab53_ok
  · exact slab54_ok
  · exact slab55_ok
  · exact slab56_ok
  · exact slab57_ok
  · exact slab58_ok
  · exact slab59_ok
  · exact slab60_ok
  · exact slab61_ok
  · exact slab62_ok
  · exact slab63_ok
  · exact slab64_ok
  · exact slab65_ok
  · exact slab66_ok
  · exact slab67_ok
  · exact slab68_ok
  · exact slab69_ok
  · exact slab70_ok
  · exact slab71_ok
  · exact slab72_ok
  · exact slab73_ok
  · exact slab74_ok
  · exact slab75_ok
  · exact slab76_ok
  · exact slab77_ok
  · exact slab78_ok
  · exact slab79_ok
  · exact slab80_ok
  · exact slab81_ok
  · exact slab82_ok
  · exact slab83_ok
  · exact slab84_ok
  · exact slab85_ok
  · exact slab86_ok
  · exact slab87_ok
  · exact slab88_ok
  · exact slab89_ok
  · exact slab90_ok
  · exact slab91_ok
  · exact slab92_ok
  · exact slab93_ok
  · exact slab94_ok
  · exact slab95_ok
  · exact slab96_ok
  · exact slab97_ok
  · exact slab98_ok
  · exact slab99_ok
  · exact slab100_ok
  · exact slab101_ok
  · exact slab102_ok
  · exact slab103_ok
  · exact slab104_ok
  · exact slab105_ok
  · exact slab106_ok
  · exact slab107_ok
  · exact slab108_ok
  · exact slab109_ok
  · exact slab110_ok
  · exact slab111_ok
  · exact slab112_ok
  · exact slab113_ok
  · exact slab114_ok
  · exact slab115_ok
  · exact slab116_ok
  · exact slab117_ok
  · exact slab118_ok
  · exact slab119_ok
  · exact slab120_ok
  · exact slab121_ok
  · exact slab122_ok
  · exact slab123_ok
  · exact slab124_ok
  · exact slab125_ok
  · exact slab126_ok
  · exact slab127_ok
  · exact slab128_ok
  · exact slab129_ok
  · exact slab130_ok
  · exact slab131_ok
  · exact slab132_ok
  · exact slab133_ok
  · exact slab134_ok
  · exact slab135_ok
  · exact slab136_ok
  · exact slab137_ok
  · exact slab138_ok
  · exact slab139_ok
  · exact slab140_ok
  · exact slab141_ok
  · exact slab142_ok
  · exact slab143_ok
  · exact slab144_ok
  · exact slab145_ok
  · exact slab146_ok
  · exact slab147_ok
  · exact slab148_ok
  · exact slab149_ok
  · exact slab150_ok
  · exact slab151_ok
  · exact slab152_ok
  · exact slab153_ok
  · exact slab154_ok
  · exact slab155_ok

theorem rowAt_facetStrip_balanced {t : Profile} (ht : OrderedInterior t)
    (hf₀ : 1 / 64 ≤ facetCoord t) (hf₁ : facetCoord t ≤ 1 / 20)
    (hτ : tau t ≤ 3 / 4) (hd : t 3 ≤ 1 / 400) : RowAt criticalQ t :=
  rowAt_facetStrip_of_scheduled_checks allChecked ht hf₀ hf₁ hτ hd

end HlawkaSchatten.BelowExponent
