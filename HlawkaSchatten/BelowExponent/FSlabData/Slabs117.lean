/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabSchedule
public import HlawkaSchatten.BelowExponent.FSlabData.Knot117Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot118Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot119Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot120Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot121Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot122Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot122Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot123Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot124Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot125Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot126Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot127Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot128Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot129Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot130Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot131Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot132Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot133Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot134Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot135Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot136Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot137Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot138Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot139Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot140Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot141Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot142Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot143Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot144Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot145Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot146Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot147Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot148Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot149Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot150Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot151Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot152Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot153Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot154Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot155Weight27
public import HlawkaSchatten.BelowExponent.FSlabData.Knot156Weight27

/-! Exact data for the weighted F-slab facet checks: `Slabs117`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public section

namespace HlawkaSchatten.BelowExponent.FSlabCheck

theorem slab117_ok : SlabChecked 117 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k117w25LowChart0_ok k117w25LowChart1_ok k117w25LowChart2_ok
  · exact checkedOfCharts k117w25HighChart0_ok k117w25HighChart1_ok k117w25HighChart2_ok
  · exact checkedOfCharts k118w25LowChart0_ok k118w25LowChart1_ok k118w25LowChart2_ok
  · exact checkedOfCharts k118w25HighChart0_ok k118w25HighChart1_ok k118w25HighChart2_ok

theorem slab118_ok : SlabChecked 118 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k118w25LowChart0_ok k118w25LowChart1_ok k118w25LowChart2_ok
  · exact checkedOfCharts k118w25HighChart0_ok k118w25HighChart1_ok k118w25HighChart2_ok
  · exact checkedOfCharts k119w25LowChart0_ok k119w25LowChart1_ok k119w25LowChart2_ok
  · exact checkedOfCharts k119w25HighChart0_ok k119w25HighChart1_ok k119w25HighChart2_ok

theorem slab119_ok : SlabChecked 119 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k119w25LowChart0_ok k119w25LowChart1_ok k119w25LowChart2_ok
  · exact checkedOfCharts k119w25HighChart0_ok k119w25HighChart1_ok k119w25HighChart2_ok
  · exact checkedOfCharts k120w25LowChart0_ok k120w25LowChart1_ok k120w25LowChart2_ok
  · exact checkedOfCharts k120w25HighChart0_ok k120w25HighChart1_ok k120w25HighChart2_ok

theorem slab120_ok : SlabChecked 120 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k120w25LowChart0_ok k120w25LowChart1_ok k120w25LowChart2_ok
  · exact checkedOfCharts k120w25HighChart0_ok k120w25HighChart1_ok k120w25HighChart2_ok
  · exact checkedOfCharts k121w25LowChart0_ok k121w25LowChart1_ok k121w25LowChart2_ok
  · exact checkedOfCharts k121w25HighChart0_ok k121w25HighChart1_ok k121w25HighChart2_ok

theorem slab121_ok : SlabChecked 121 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k121w25LowChart0_ok k121w25LowChart1_ok k121w25LowChart2_ok
  · exact checkedOfCharts k121w25HighChart0_ok k121w25HighChart1_ok k121w25HighChart2_ok
  · exact checkedOfCharts k122w25LowChart0_ok k122w25LowChart1_ok k122w25LowChart2_ok
  · exact checkedOfCharts k122w25HighChart0_ok k122w25HighChart1_ok k122w25HighChart2_ok

theorem slab122_ok : SlabChecked 122 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k122w27LowChart0_ok k122w27LowChart1_ok k122w27LowChart2_ok
  · exact checkedOfCharts k122w27HighChart0_ok k122w27HighChart1_ok k122w27HighChart2_ok
  · exact checkedOfCharts k123w27LowChart0_ok k123w27LowChart1_ok k123w27LowChart2_ok
  · exact checkedOfCharts k123w27HighChart0_ok k123w27HighChart1_ok k123w27HighChart2_ok

theorem slab123_ok : SlabChecked 123 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k123w27LowChart0_ok k123w27LowChart1_ok k123w27LowChart2_ok
  · exact checkedOfCharts k123w27HighChart0_ok k123w27HighChart1_ok k123w27HighChart2_ok
  · exact checkedOfCharts k124w27LowChart0_ok k124w27LowChart1_ok k124w27LowChart2_ok
  · exact checkedOfCharts k124w27HighChart0_ok k124w27HighChart1_ok k124w27HighChart2_ok

theorem slab124_ok : SlabChecked 124 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k124w27LowChart0_ok k124w27LowChart1_ok k124w27LowChart2_ok
  · exact checkedOfCharts k124w27HighChart0_ok k124w27HighChart1_ok k124w27HighChart2_ok
  · exact checkedOfCharts k125w27LowChart0_ok k125w27LowChart1_ok k125w27LowChart2_ok
  · exact checkedOfCharts k125w27HighChart0_ok k125w27HighChart1_ok k125w27HighChart2_ok

theorem slab125_ok : SlabChecked 125 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k125w27LowChart0_ok k125w27LowChart1_ok k125w27LowChart2_ok
  · exact checkedOfCharts k125w27HighChart0_ok k125w27HighChart1_ok k125w27HighChart2_ok
  · exact checkedOfCharts k126w27LowChart0_ok k126w27LowChart1_ok k126w27LowChart2_ok
  · exact checkedOfCharts k126w27HighChart0_ok k126w27HighChart1_ok k126w27HighChart2_ok

theorem slab126_ok : SlabChecked 126 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k126w27LowChart0_ok k126w27LowChart1_ok k126w27LowChart2_ok
  · exact checkedOfCharts k126w27HighChart0_ok k126w27HighChart1_ok k126w27HighChart2_ok
  · exact checkedOfCharts k127w27LowChart0_ok k127w27LowChart1_ok k127w27LowChart2_ok
  · exact checkedOfCharts k127w27HighChart0_ok k127w27HighChart1_ok k127w27HighChart2_ok

theorem slab127_ok : SlabChecked 127 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k127w27LowChart0_ok k127w27LowChart1_ok k127w27LowChart2_ok
  · exact checkedOfCharts k127w27HighChart0_ok k127w27HighChart1_ok k127w27HighChart2_ok
  · exact checkedOfCharts k128w27LowChart0_ok k128w27LowChart1_ok k128w27LowChart2_ok
  · exact checkedOfCharts k128w27HighChart0_ok k128w27HighChart1_ok k128w27HighChart2_ok

theorem slab128_ok : SlabChecked 128 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k128w27LowChart0_ok k128w27LowChart1_ok k128w27LowChart2_ok
  · exact checkedOfCharts k128w27HighChart0_ok k128w27HighChart1_ok k128w27HighChart2_ok
  · exact checkedOfCharts k129w27LowChart0_ok k129w27LowChart1_ok k129w27LowChart2_ok
  · exact checkedOfCharts k129w27HighChart0_ok k129w27HighChart1_ok k129w27HighChart2_ok

theorem slab129_ok : SlabChecked 129 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k129w27LowChart0_ok k129w27LowChart1_ok k129w27LowChart2_ok
  · exact checkedOfCharts k129w27HighChart0_ok k129w27HighChart1_ok k129w27HighChart2_ok
  · exact checkedOfCharts k130w27LowChart0_ok k130w27LowChart1_ok k130w27LowChart2_ok
  · exact checkedOfCharts k130w27HighChart0_ok k130w27HighChart1_ok k130w27HighChart2_ok

theorem slab130_ok : SlabChecked 130 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k130w27LowChart0_ok k130w27LowChart1_ok k130w27LowChart2_ok
  · exact checkedOfCharts k130w27HighChart0_ok k130w27HighChart1_ok k130w27HighChart2_ok
  · exact checkedOfCharts k131w27LowChart0_ok k131w27LowChart1_ok k131w27LowChart2_ok
  · exact checkedOfCharts k131w27HighChart0_ok k131w27HighChart1_ok k131w27HighChart2_ok

theorem slab131_ok : SlabChecked 131 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k131w27LowChart0_ok k131w27LowChart1_ok k131w27LowChart2_ok
  · exact checkedOfCharts k131w27HighChart0_ok k131w27HighChart1_ok k131w27HighChart2_ok
  · exact checkedOfCharts k132w27LowChart0_ok k132w27LowChart1_ok k132w27LowChart2_ok
  · exact checkedOfCharts k132w27HighChart0_ok k132w27HighChart1_ok k132w27HighChart2_ok

theorem slab132_ok : SlabChecked 132 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k132w27LowChart0_ok k132w27LowChart1_ok k132w27LowChart2_ok
  · exact checkedOfCharts k132w27HighChart0_ok k132w27HighChart1_ok k132w27HighChart2_ok
  · exact checkedOfCharts k133w27LowChart0_ok k133w27LowChart1_ok k133w27LowChart2_ok
  · exact checkedOfCharts k133w27HighChart0_ok k133w27HighChart1_ok k133w27HighChart2_ok

theorem slab133_ok : SlabChecked 133 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k133w27LowChart0_ok k133w27LowChart1_ok k133w27LowChart2_ok
  · exact checkedOfCharts k133w27HighChart0_ok k133w27HighChart1_ok k133w27HighChart2_ok
  · exact checkedOfCharts k134w27LowChart0_ok k134w27LowChart1_ok k134w27LowChart2_ok
  · exact checkedOfCharts k134w27HighChart0_ok k134w27HighChart1_ok k134w27HighChart2_ok

theorem slab134_ok : SlabChecked 134 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k134w27LowChart0_ok k134w27LowChart1_ok k134w27LowChart2_ok
  · exact checkedOfCharts k134w27HighChart0_ok k134w27HighChart1_ok k134w27HighChart2_ok
  · exact checkedOfCharts k135w27LowChart0_ok k135w27LowChart1_ok k135w27LowChart2_ok
  · exact checkedOfCharts k135w27HighChart0_ok k135w27HighChart1_ok k135w27HighChart2_ok

theorem slab135_ok : SlabChecked 135 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k135w27LowChart0_ok k135w27LowChart1_ok k135w27LowChart2_ok
  · exact checkedOfCharts k135w27HighChart0_ok k135w27HighChart1_ok k135w27HighChart2_ok
  · exact checkedOfCharts k136w27LowChart0_ok k136w27LowChart1_ok k136w27LowChart2_ok
  · exact checkedOfCharts k136w27HighChart0_ok k136w27HighChart1_ok k136w27HighChart2_ok

theorem slab136_ok : SlabChecked 136 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k136w27LowChart0_ok k136w27LowChart1_ok k136w27LowChart2_ok
  · exact checkedOfCharts k136w27HighChart0_ok k136w27HighChart1_ok k136w27HighChart2_ok
  · exact checkedOfCharts k137w27LowChart0_ok k137w27LowChart1_ok k137w27LowChart2_ok
  · exact checkedOfCharts k137w27HighChart0_ok k137w27HighChart1_ok k137w27HighChart2_ok

theorem slab137_ok : SlabChecked 137 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k137w27LowChart0_ok k137w27LowChart1_ok k137w27LowChart2_ok
  · exact checkedOfCharts k137w27HighChart0_ok k137w27HighChart1_ok k137w27HighChart2_ok
  · exact checkedOfCharts k138w27LowChart0_ok k138w27LowChart1_ok k138w27LowChart2_ok
  · exact checkedOfCharts k138w27HighChart0_ok k138w27HighChart1_ok k138w27HighChart2_ok

theorem slab138_ok : SlabChecked 138 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k138w27LowChart0_ok k138w27LowChart1_ok k138w27LowChart2_ok
  · exact checkedOfCharts k138w27HighChart0_ok k138w27HighChart1_ok k138w27HighChart2_ok
  · exact checkedOfCharts k139w27LowChart0_ok k139w27LowChart1_ok k139w27LowChart2_ok
  · exact checkedOfCharts k139w27HighChart0_ok k139w27HighChart1_ok k139w27HighChart2_ok

theorem slab139_ok : SlabChecked 139 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k139w27LowChart0_ok k139w27LowChart1_ok k139w27LowChart2_ok
  · exact checkedOfCharts k139w27HighChart0_ok k139w27HighChart1_ok k139w27HighChart2_ok
  · exact checkedOfCharts k140w27LowChart0_ok k140w27LowChart1_ok k140w27LowChart2_ok
  · exact checkedOfCharts k140w27HighChart0_ok k140w27HighChart1_ok k140w27HighChart2_ok

theorem slab140_ok : SlabChecked 140 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k140w27LowChart0_ok k140w27LowChart1_ok k140w27LowChart2_ok
  · exact checkedOfCharts k140w27HighChart0_ok k140w27HighChart1_ok k140w27HighChart2_ok
  · exact checkedOfCharts k141w27LowChart0_ok k141w27LowChart1_ok k141w27LowChart2_ok
  · exact checkedOfCharts k141w27HighChart0_ok k141w27HighChart1_ok k141w27HighChart2_ok

theorem slab141_ok : SlabChecked 141 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k141w27LowChart0_ok k141w27LowChart1_ok k141w27LowChart2_ok
  · exact checkedOfCharts k141w27HighChart0_ok k141w27HighChart1_ok k141w27HighChart2_ok
  · exact checkedOfCharts k142w27LowChart0_ok k142w27LowChart1_ok k142w27LowChart2_ok
  · exact checkedOfCharts k142w27HighChart0_ok k142w27HighChart1_ok k142w27HighChart2_ok

theorem slab142_ok : SlabChecked 142 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k142w27LowChart0_ok k142w27LowChart1_ok k142w27LowChart2_ok
  · exact checkedOfCharts k142w27HighChart0_ok k142w27HighChart1_ok k142w27HighChart2_ok
  · exact checkedOfCharts k143w27LowChart0_ok k143w27LowChart1_ok k143w27LowChart2_ok
  · exact checkedOfCharts k143w27HighChart0_ok k143w27HighChart1_ok k143w27HighChart2_ok

theorem slab143_ok : SlabChecked 143 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k143w27LowChart0_ok k143w27LowChart1_ok k143w27LowChart2_ok
  · exact checkedOfCharts k143w27HighChart0_ok k143w27HighChart1_ok k143w27HighChart2_ok
  · exact checkedOfCharts k144w27LowChart0_ok k144w27LowChart1_ok k144w27LowChart2_ok
  · exact checkedOfCharts k144w27HighChart0_ok k144w27HighChart1_ok k144w27HighChart2_ok

theorem slab144_ok : SlabChecked 144 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k144w27LowChart0_ok k144w27LowChart1_ok k144w27LowChart2_ok
  · exact checkedOfCharts k144w27HighChart0_ok k144w27HighChart1_ok k144w27HighChart2_ok
  · exact checkedOfCharts k145w27LowChart0_ok k145w27LowChart1_ok k145w27LowChart2_ok
  · exact checkedOfCharts k145w27HighChart0_ok k145w27HighChart1_ok k145w27HighChart2_ok

theorem slab145_ok : SlabChecked 145 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k145w27LowChart0_ok k145w27LowChart1_ok k145w27LowChart2_ok
  · exact checkedOfCharts k145w27HighChart0_ok k145w27HighChart1_ok k145w27HighChart2_ok
  · exact checkedOfCharts k146w27LowChart0_ok k146w27LowChart1_ok k146w27LowChart2_ok
  · exact checkedOfCharts k146w27HighChart0_ok k146w27HighChart1_ok k146w27HighChart2_ok

theorem slab146_ok : SlabChecked 146 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k146w27LowChart0_ok k146w27LowChart1_ok k146w27LowChart2_ok
  · exact checkedOfCharts k146w27HighChart0_ok k146w27HighChart1_ok k146w27HighChart2_ok
  · exact checkedOfCharts k147w27LowChart0_ok k147w27LowChart1_ok k147w27LowChart2_ok
  · exact checkedOfCharts k147w27HighChart0_ok k147w27HighChart1_ok k147w27HighChart2_ok

theorem slab147_ok : SlabChecked 147 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k147w27LowChart0_ok k147w27LowChart1_ok k147w27LowChart2_ok
  · exact checkedOfCharts k147w27HighChart0_ok k147w27HighChart1_ok k147w27HighChart2_ok
  · exact checkedOfCharts k148w27LowChart0_ok k148w27LowChart1_ok k148w27LowChart2_ok
  · exact checkedOfCharts k148w27HighChart0_ok k148w27HighChart1_ok k148w27HighChart2_ok

theorem slab148_ok : SlabChecked 148 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k148w27LowChart0_ok k148w27LowChart1_ok k148w27LowChart2_ok
  · exact checkedOfCharts k148w27HighChart0_ok k148w27HighChart1_ok k148w27HighChart2_ok
  · exact checkedOfCharts k149w27LowChart0_ok k149w27LowChart1_ok k149w27LowChart2_ok
  · exact checkedOfCharts k149w27HighChart0_ok k149w27HighChart1_ok k149w27HighChart2_ok

theorem slab149_ok : SlabChecked 149 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k149w27LowChart0_ok k149w27LowChart1_ok k149w27LowChart2_ok
  · exact checkedOfCharts k149w27HighChart0_ok k149w27HighChart1_ok k149w27HighChart2_ok
  · exact checkedOfCharts k150w27LowChart0_ok k150w27LowChart1_ok k150w27LowChart2_ok
  · exact checkedOfCharts k150w27HighChart0_ok k150w27HighChart1_ok k150w27HighChart2_ok

theorem slab150_ok : SlabChecked 150 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k150w27LowChart0_ok k150w27LowChart1_ok k150w27LowChart2_ok
  · exact checkedOfCharts k150w27HighChart0_ok k150w27HighChart1_ok k150w27HighChart2_ok
  · exact checkedOfCharts k151w27LowChart0_ok k151w27LowChart1_ok k151w27LowChart2_ok
  · exact checkedOfCharts k151w27HighChart0_ok k151w27HighChart1_ok k151w27HighChart2_ok

theorem slab151_ok : SlabChecked 151 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k151w27LowChart0_ok k151w27LowChart1_ok k151w27LowChart2_ok
  · exact checkedOfCharts k151w27HighChart0_ok k151w27HighChart1_ok k151w27HighChart2_ok
  · exact checkedOfCharts k152w27LowChart0_ok k152w27LowChart1_ok k152w27LowChart2_ok
  · exact checkedOfCharts k152w27HighChart0_ok k152w27HighChart1_ok k152w27HighChart2_ok

theorem slab152_ok : SlabChecked 152 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k152w27LowChart0_ok k152w27LowChart1_ok k152w27LowChart2_ok
  · exact checkedOfCharts k152w27HighChart0_ok k152w27HighChart1_ok k152w27HighChart2_ok
  · exact checkedOfCharts k153w27LowChart0_ok k153w27LowChart1_ok k153w27LowChart2_ok
  · exact checkedOfCharts k153w27HighChart0_ok k153w27HighChart1_ok k153w27HighChart2_ok

theorem slab153_ok : SlabChecked 153 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k153w27LowChart0_ok k153w27LowChart1_ok k153w27LowChart2_ok
  · exact checkedOfCharts k153w27HighChart0_ok k153w27HighChart1_ok k153w27HighChart2_ok
  · exact checkedOfCharts k154w27LowChart0_ok k154w27LowChart1_ok k154w27LowChart2_ok
  · exact checkedOfCharts k154w27HighChart0_ok k154w27HighChart1_ok k154w27HighChart2_ok

theorem slab154_ok : SlabChecked 154 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k154w27LowChart0_ok k154w27LowChart1_ok k154w27LowChart2_ok
  · exact checkedOfCharts k154w27HighChart0_ok k154w27HighChart1_ok k154w27HighChart2_ok
  · exact checkedOfCharts k155w27LowChart0_ok k155w27LowChart1_ok k155w27LowChart2_ok
  · exact checkedOfCharts k155w27HighChart0_ok k155w27HighChart1_ok k155w27HighChart2_ok

theorem slab155_ok : SlabChecked 155 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k155w27LowChart0_ok k155w27LowChart1_ok k155w27LowChart2_ok
  · exact checkedOfCharts k155w27HighChart0_ok k155w27HighChart1_ok k155w27HighChart2_ok
  · exact checkedOfCharts k156w27LowChart0_ok k156w27LowChart1_ok k156w27LowChart2_ok
  · exact checkedOfCharts k156w27HighChart0_ok k156w27HighChart1_ok k156w27HighChart2_ok

end HlawkaSchatten.BelowExponent.FSlabCheck
