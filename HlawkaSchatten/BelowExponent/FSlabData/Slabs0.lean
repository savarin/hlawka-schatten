/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabSchedule
public import HlawkaSchatten.BelowExponent.FSlabData.Knot0Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot1Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot2Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot3Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot4Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot5Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot6Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot7Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot8Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot9Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot10Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot11Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot12Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot13Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot14Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot15Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot16Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot17Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot18Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot19Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot20Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot21Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot22Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot23Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot24Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot25Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot26Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot27Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot28Weight21
public import HlawkaSchatten.BelowExponent.FSlabData.Knot28Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot29Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot30Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot31Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot32Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot33Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot34Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot35Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot36Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot37Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot38Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot39Weight23

/-! Exact data for the weighted F-slab facet checks: `Slabs0`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public section

namespace HlawkaSchatten.BelowExponent.FSlabCheck

theorem slab0_ok : SlabChecked 0 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k0w21LowChart0_ok k0w21LowChart1_ok k0w21LowChart2_ok
  · exact checkedOfCharts k0w21HighChart0_ok k0w21HighChart1_ok k0w21HighChart2_ok
  · exact checkedOfCharts k1w21LowChart0_ok k1w21LowChart1_ok k1w21LowChart2_ok
  · exact checkedOfCharts k1w21HighChart0_ok k1w21HighChart1_ok k1w21HighChart2_ok

theorem slab1_ok : SlabChecked 1 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k1w21LowChart0_ok k1w21LowChart1_ok k1w21LowChart2_ok
  · exact checkedOfCharts k1w21HighChart0_ok k1w21HighChart1_ok k1w21HighChart2_ok
  · exact checkedOfCharts k2w21LowChart0_ok k2w21LowChart1_ok k2w21LowChart2_ok
  · exact checkedOfCharts k2w21HighChart0_ok k2w21HighChart1_ok k2w21HighChart2_ok

theorem slab2_ok : SlabChecked 2 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k2w21LowChart0_ok k2w21LowChart1_ok k2w21LowChart2_ok
  · exact checkedOfCharts k2w21HighChart0_ok k2w21HighChart1_ok k2w21HighChart2_ok
  · exact checkedOfCharts k3w21LowChart0_ok k3w21LowChart1_ok k3w21LowChart2_ok
  · exact checkedOfCharts k3w21HighChart0_ok k3w21HighChart1_ok k3w21HighChart2_ok

theorem slab3_ok : SlabChecked 3 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k3w21LowChart0_ok k3w21LowChart1_ok k3w21LowChart2_ok
  · exact checkedOfCharts k3w21HighChart0_ok k3w21HighChart1_ok k3w21HighChart2_ok
  · exact checkedOfCharts k4w21LowChart0_ok k4w21LowChart1_ok k4w21LowChart2_ok
  · exact checkedOfCharts k4w21HighChart0_ok k4w21HighChart1_ok k4w21HighChart2_ok

theorem slab4_ok : SlabChecked 4 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k4w21LowChart0_ok k4w21LowChart1_ok k4w21LowChart2_ok
  · exact checkedOfCharts k4w21HighChart0_ok k4w21HighChart1_ok k4w21HighChart2_ok
  · exact checkedOfCharts k5w21LowChart0_ok k5w21LowChart1_ok k5w21LowChart2_ok
  · exact checkedOfCharts k5w21HighChart0_ok k5w21HighChart1_ok k5w21HighChart2_ok

theorem slab5_ok : SlabChecked 5 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k5w21LowChart0_ok k5w21LowChart1_ok k5w21LowChart2_ok
  · exact checkedOfCharts k5w21HighChart0_ok k5w21HighChart1_ok k5w21HighChart2_ok
  · exact checkedOfCharts k6w21LowChart0_ok k6w21LowChart1_ok k6w21LowChart2_ok
  · exact checkedOfCharts k6w21HighChart0_ok k6w21HighChart1_ok k6w21HighChart2_ok

theorem slab6_ok : SlabChecked 6 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k6w21LowChart0_ok k6w21LowChart1_ok k6w21LowChart2_ok
  · exact checkedOfCharts k6w21HighChart0_ok k6w21HighChart1_ok k6w21HighChart2_ok
  · exact checkedOfCharts k7w21LowChart0_ok k7w21LowChart1_ok k7w21LowChart2_ok
  · exact checkedOfCharts k7w21HighChart0_ok k7w21HighChart1_ok k7w21HighChart2_ok

theorem slab7_ok : SlabChecked 7 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k7w21LowChart0_ok k7w21LowChart1_ok k7w21LowChart2_ok
  · exact checkedOfCharts k7w21HighChart0_ok k7w21HighChart1_ok k7w21HighChart2_ok
  · exact checkedOfCharts k8w21LowChart0_ok k8w21LowChart1_ok k8w21LowChart2_ok
  · exact checkedOfCharts k8w21HighChart0_ok k8w21HighChart1_ok k8w21HighChart2_ok

theorem slab8_ok : SlabChecked 8 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k8w21LowChart0_ok k8w21LowChart1_ok k8w21LowChart2_ok
  · exact checkedOfCharts k8w21HighChart0_ok k8w21HighChart1_ok k8w21HighChart2_ok
  · exact checkedOfCharts k9w21LowChart0_ok k9w21LowChart1_ok k9w21LowChart2_ok
  · exact checkedOfCharts k9w21HighChart0_ok k9w21HighChart1_ok k9w21HighChart2_ok

theorem slab9_ok : SlabChecked 9 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k9w21LowChart0_ok k9w21LowChart1_ok k9w21LowChart2_ok
  · exact checkedOfCharts k9w21HighChart0_ok k9w21HighChart1_ok k9w21HighChart2_ok
  · exact checkedOfCharts k10w21LowChart0_ok k10w21LowChart1_ok k10w21LowChart2_ok
  · exact checkedOfCharts k10w21HighChart0_ok k10w21HighChart1_ok k10w21HighChart2_ok

theorem slab10_ok : SlabChecked 10 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k10w21LowChart0_ok k10w21LowChart1_ok k10w21LowChart2_ok
  · exact checkedOfCharts k10w21HighChart0_ok k10w21HighChart1_ok k10w21HighChart2_ok
  · exact checkedOfCharts k11w21LowChart0_ok k11w21LowChart1_ok k11w21LowChart2_ok
  · exact checkedOfCharts k11w21HighChart0_ok k11w21HighChart1_ok k11w21HighChart2_ok

theorem slab11_ok : SlabChecked 11 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k11w21LowChart0_ok k11w21LowChart1_ok k11w21LowChart2_ok
  · exact checkedOfCharts k11w21HighChart0_ok k11w21HighChart1_ok k11w21HighChart2_ok
  · exact checkedOfCharts k12w21LowChart0_ok k12w21LowChart1_ok k12w21LowChart2_ok
  · exact checkedOfCharts k12w21HighChart0_ok k12w21HighChart1_ok k12w21HighChart2_ok

theorem slab12_ok : SlabChecked 12 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k12w21LowChart0_ok k12w21LowChart1_ok k12w21LowChart2_ok
  · exact checkedOfCharts k12w21HighChart0_ok k12w21HighChart1_ok k12w21HighChart2_ok
  · exact checkedOfCharts k13w21LowChart0_ok k13w21LowChart1_ok k13w21LowChart2_ok
  · exact checkedOfCharts k13w21HighChart0_ok k13w21HighChart1_ok k13w21HighChart2_ok

theorem slab13_ok : SlabChecked 13 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k13w21LowChart0_ok k13w21LowChart1_ok k13w21LowChart2_ok
  · exact checkedOfCharts k13w21HighChart0_ok k13w21HighChart1_ok k13w21HighChart2_ok
  · exact checkedOfCharts k14w21LowChart0_ok k14w21LowChart1_ok k14w21LowChart2_ok
  · exact checkedOfCharts k14w21HighChart0_ok k14w21HighChart1_ok k14w21HighChart2_ok

theorem slab14_ok : SlabChecked 14 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k14w21LowChart0_ok k14w21LowChart1_ok k14w21LowChart2_ok
  · exact checkedOfCharts k14w21HighChart0_ok k14w21HighChart1_ok k14w21HighChart2_ok
  · exact checkedOfCharts k15w21LowChart0_ok k15w21LowChart1_ok k15w21LowChart2_ok
  · exact checkedOfCharts k15w21HighChart0_ok k15w21HighChart1_ok k15w21HighChart2_ok

theorem slab15_ok : SlabChecked 15 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k15w21LowChart0_ok k15w21LowChart1_ok k15w21LowChart2_ok
  · exact checkedOfCharts k15w21HighChart0_ok k15w21HighChart1_ok k15w21HighChart2_ok
  · exact checkedOfCharts k16w21LowChart0_ok k16w21LowChart1_ok k16w21LowChart2_ok
  · exact checkedOfCharts k16w21HighChart0_ok k16w21HighChart1_ok k16w21HighChart2_ok

theorem slab16_ok : SlabChecked 16 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k16w21LowChart0_ok k16w21LowChart1_ok k16w21LowChart2_ok
  · exact checkedOfCharts k16w21HighChart0_ok k16w21HighChart1_ok k16w21HighChart2_ok
  · exact checkedOfCharts k17w21LowChart0_ok k17w21LowChart1_ok k17w21LowChart2_ok
  · exact checkedOfCharts k17w21HighChart0_ok k17w21HighChart1_ok k17w21HighChart2_ok

theorem slab17_ok : SlabChecked 17 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k17w21LowChart0_ok k17w21LowChart1_ok k17w21LowChart2_ok
  · exact checkedOfCharts k17w21HighChart0_ok k17w21HighChart1_ok k17w21HighChart2_ok
  · exact checkedOfCharts k18w21LowChart0_ok k18w21LowChart1_ok k18w21LowChart2_ok
  · exact checkedOfCharts k18w21HighChart0_ok k18w21HighChart1_ok k18w21HighChart2_ok

theorem slab18_ok : SlabChecked 18 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k18w21LowChart0_ok k18w21LowChart1_ok k18w21LowChart2_ok
  · exact checkedOfCharts k18w21HighChart0_ok k18w21HighChart1_ok k18w21HighChart2_ok
  · exact checkedOfCharts k19w21LowChart0_ok k19w21LowChart1_ok k19w21LowChart2_ok
  · exact checkedOfCharts k19w21HighChart0_ok k19w21HighChart1_ok k19w21HighChart2_ok

theorem slab19_ok : SlabChecked 19 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k19w21LowChart0_ok k19w21LowChart1_ok k19w21LowChart2_ok
  · exact checkedOfCharts k19w21HighChart0_ok k19w21HighChart1_ok k19w21HighChart2_ok
  · exact checkedOfCharts k20w21LowChart0_ok k20w21LowChart1_ok k20w21LowChart2_ok
  · exact checkedOfCharts k20w21HighChart0_ok k20w21HighChart1_ok k20w21HighChart2_ok

theorem slab20_ok : SlabChecked 20 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k20w21LowChart0_ok k20w21LowChart1_ok k20w21LowChart2_ok
  · exact checkedOfCharts k20w21HighChart0_ok k20w21HighChart1_ok k20w21HighChart2_ok
  · exact checkedOfCharts k21w21LowChart0_ok k21w21LowChart1_ok k21w21LowChart2_ok
  · exact checkedOfCharts k21w21HighChart0_ok k21w21HighChart1_ok k21w21HighChart2_ok

theorem slab21_ok : SlabChecked 21 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k21w21LowChart0_ok k21w21LowChart1_ok k21w21LowChart2_ok
  · exact checkedOfCharts k21w21HighChart0_ok k21w21HighChart1_ok k21w21HighChart2_ok
  · exact checkedOfCharts k22w21LowChart0_ok k22w21LowChart1_ok k22w21LowChart2_ok
  · exact checkedOfCharts k22w21HighChart0_ok k22w21HighChart1_ok k22w21HighChart2_ok

theorem slab22_ok : SlabChecked 22 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k22w21LowChart0_ok k22w21LowChart1_ok k22w21LowChart2_ok
  · exact checkedOfCharts k22w21HighChart0_ok k22w21HighChart1_ok k22w21HighChart2_ok
  · exact checkedOfCharts k23w21LowChart0_ok k23w21LowChart1_ok k23w21LowChart2_ok
  · exact checkedOfCharts k23w21HighChart0_ok k23w21HighChart1_ok k23w21HighChart2_ok

theorem slab23_ok : SlabChecked 23 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k23w21LowChart0_ok k23w21LowChart1_ok k23w21LowChart2_ok
  · exact checkedOfCharts k23w21HighChart0_ok k23w21HighChart1_ok k23w21HighChart2_ok
  · exact checkedOfCharts k24w21LowChart0_ok k24w21LowChart1_ok k24w21LowChart2_ok
  · exact checkedOfCharts k24w21HighChart0_ok k24w21HighChart1_ok k24w21HighChart2_ok

theorem slab24_ok : SlabChecked 24 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k24w21LowChart0_ok k24w21LowChart1_ok k24w21LowChart2_ok
  · exact checkedOfCharts k24w21HighChart0_ok k24w21HighChart1_ok k24w21HighChart2_ok
  · exact checkedOfCharts k25w21LowChart0_ok k25w21LowChart1_ok k25w21LowChart2_ok
  · exact checkedOfCharts k25w21HighChart0_ok k25w21HighChart1_ok k25w21HighChart2_ok

theorem slab25_ok : SlabChecked 25 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k25w21LowChart0_ok k25w21LowChart1_ok k25w21LowChart2_ok
  · exact checkedOfCharts k25w21HighChart0_ok k25w21HighChart1_ok k25w21HighChart2_ok
  · exact checkedOfCharts k26w21LowChart0_ok k26w21LowChart1_ok k26w21LowChart2_ok
  · exact checkedOfCharts k26w21HighChart0_ok k26w21HighChart1_ok k26w21HighChart2_ok

theorem slab26_ok : SlabChecked 26 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k26w21LowChart0_ok k26w21LowChart1_ok k26w21LowChart2_ok
  · exact checkedOfCharts k26w21HighChart0_ok k26w21HighChart1_ok k26w21HighChart2_ok
  · exact checkedOfCharts k27w21LowChart0_ok k27w21LowChart1_ok k27w21LowChart2_ok
  · exact checkedOfCharts k27w21HighChart0_ok k27w21HighChart1_ok k27w21HighChart2_ok

theorem slab27_ok : SlabChecked 27 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k27w21LowChart0_ok k27w21LowChart1_ok k27w21LowChart2_ok
  · exact checkedOfCharts k27w21HighChart0_ok k27w21HighChart1_ok k27w21HighChart2_ok
  · exact checkedOfCharts k28w21LowChart0_ok k28w21LowChart1_ok k28w21LowChart2_ok
  · exact checkedOfCharts k28w21HighChart0_ok k28w21HighChart1_ok k28w21HighChart2_ok

theorem slab28_ok : SlabChecked 28 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k28w23LowChart0_ok k28w23LowChart1_ok k28w23LowChart2_ok
  · exact checkedOfCharts k28w23HighChart0_ok k28w23HighChart1_ok k28w23HighChart2_ok
  · exact checkedOfCharts k29w23LowChart0_ok k29w23LowChart1_ok k29w23LowChart2_ok
  · exact checkedOfCharts k29w23HighChart0_ok k29w23HighChart1_ok k29w23HighChart2_ok

theorem slab29_ok : SlabChecked 29 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k29w23LowChart0_ok k29w23LowChart1_ok k29w23LowChart2_ok
  · exact checkedOfCharts k29w23HighChart0_ok k29w23HighChart1_ok k29w23HighChart2_ok
  · exact checkedOfCharts k30w23LowChart0_ok k30w23LowChart1_ok k30w23LowChart2_ok
  · exact checkedOfCharts k30w23HighChart0_ok k30w23HighChart1_ok k30w23HighChart2_ok

theorem slab30_ok : SlabChecked 30 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k30w23LowChart0_ok k30w23LowChart1_ok k30w23LowChart2_ok
  · exact checkedOfCharts k30w23HighChart0_ok k30w23HighChart1_ok k30w23HighChart2_ok
  · exact checkedOfCharts k31w23LowChart0_ok k31w23LowChart1_ok k31w23LowChart2_ok
  · exact checkedOfCharts k31w23HighChart0_ok k31w23HighChart1_ok k31w23HighChart2_ok

theorem slab31_ok : SlabChecked 31 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k31w23LowChart0_ok k31w23LowChart1_ok k31w23LowChart2_ok
  · exact checkedOfCharts k31w23HighChart0_ok k31w23HighChart1_ok k31w23HighChart2_ok
  · exact checkedOfCharts k32w23LowChart0_ok k32w23LowChart1_ok k32w23LowChart2_ok
  · exact checkedOfCharts k32w23HighChart0_ok k32w23HighChart1_ok k32w23HighChart2_ok

theorem slab32_ok : SlabChecked 32 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k32w23LowChart0_ok k32w23LowChart1_ok k32w23LowChart2_ok
  · exact checkedOfCharts k32w23HighChart0_ok k32w23HighChart1_ok k32w23HighChart2_ok
  · exact checkedOfCharts k33w23LowChart0_ok k33w23LowChart1_ok k33w23LowChart2_ok
  · exact checkedOfCharts k33w23HighChart0_ok k33w23HighChart1_ok k33w23HighChart2_ok

theorem slab33_ok : SlabChecked 33 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k33w23LowChart0_ok k33w23LowChart1_ok k33w23LowChart2_ok
  · exact checkedOfCharts k33w23HighChart0_ok k33w23HighChart1_ok k33w23HighChart2_ok
  · exact checkedOfCharts k34w23LowChart0_ok k34w23LowChart1_ok k34w23LowChart2_ok
  · exact checkedOfCharts k34w23HighChart0_ok k34w23HighChart1_ok k34w23HighChart2_ok

theorem slab34_ok : SlabChecked 34 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k34w23LowChart0_ok k34w23LowChart1_ok k34w23LowChart2_ok
  · exact checkedOfCharts k34w23HighChart0_ok k34w23HighChart1_ok k34w23HighChart2_ok
  · exact checkedOfCharts k35w23LowChart0_ok k35w23LowChart1_ok k35w23LowChart2_ok
  · exact checkedOfCharts k35w23HighChart0_ok k35w23HighChart1_ok k35w23HighChart2_ok

theorem slab35_ok : SlabChecked 35 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k35w23LowChart0_ok k35w23LowChart1_ok k35w23LowChart2_ok
  · exact checkedOfCharts k35w23HighChart0_ok k35w23HighChart1_ok k35w23HighChart2_ok
  · exact checkedOfCharts k36w23LowChart0_ok k36w23LowChart1_ok k36w23LowChart2_ok
  · exact checkedOfCharts k36w23HighChart0_ok k36w23HighChart1_ok k36w23HighChart2_ok

theorem slab36_ok : SlabChecked 36 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k36w23LowChart0_ok k36w23LowChart1_ok k36w23LowChart2_ok
  · exact checkedOfCharts k36w23HighChart0_ok k36w23HighChart1_ok k36w23HighChart2_ok
  · exact checkedOfCharts k37w23LowChart0_ok k37w23LowChart1_ok k37w23LowChart2_ok
  · exact checkedOfCharts k37w23HighChart0_ok k37w23HighChart1_ok k37w23HighChart2_ok

theorem slab37_ok : SlabChecked 37 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k37w23LowChart0_ok k37w23LowChart1_ok k37w23LowChart2_ok
  · exact checkedOfCharts k37w23HighChart0_ok k37w23HighChart1_ok k37w23HighChart2_ok
  · exact checkedOfCharts k38w23LowChart0_ok k38w23LowChart1_ok k38w23LowChart2_ok
  · exact checkedOfCharts k38w23HighChart0_ok k38w23HighChart1_ok k38w23HighChart2_ok

theorem slab38_ok : SlabChecked 38 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k38w23LowChart0_ok k38w23LowChart1_ok k38w23LowChart2_ok
  · exact checkedOfCharts k38w23HighChart0_ok k38w23HighChart1_ok k38w23HighChart2_ok
  · exact checkedOfCharts k39w23LowChart0_ok k39w23LowChart1_ok k39w23LowChart2_ok
  · exact checkedOfCharts k39w23HighChart0_ok k39w23HighChart1_ok k39w23HighChart2_ok

end HlawkaSchatten.BelowExponent.FSlabCheck
