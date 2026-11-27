/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabSchedule
public import HlawkaSchatten.BelowExponent.FSlabData.Knot39Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot40Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot41Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot42Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot43Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot44Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot45Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot46Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot47Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot48Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot49Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot50Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot51Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot52Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot53Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot54Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot55Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot56Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot57Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot58Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot59Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot60Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot61Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot62Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot63Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot64Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot65Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot66Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot67Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot68Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot69Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot70Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot71Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot72Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot73Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot74Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot75Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot76Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot77Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot78Weight23

/-! Exact data for the weighted F-slab facet checks: `Slabs39`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public section

namespace HlawkaSchatten.BelowExponent.FSlabCheck

theorem slab39_ok : SlabChecked 39 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k39w23LowChart0_ok k39w23LowChart1_ok k39w23LowChart2_ok
  · exact checkedOfCharts k39w23HighChart0_ok k39w23HighChart1_ok k39w23HighChart2_ok
  · exact checkedOfCharts k40w23LowChart0_ok k40w23LowChart1_ok k40w23LowChart2_ok
  · exact checkedOfCharts k40w23HighChart0_ok k40w23HighChart1_ok k40w23HighChart2_ok

theorem slab40_ok : SlabChecked 40 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k40w23LowChart0_ok k40w23LowChart1_ok k40w23LowChart2_ok
  · exact checkedOfCharts k40w23HighChart0_ok k40w23HighChart1_ok k40w23HighChart2_ok
  · exact checkedOfCharts k41w23LowChart0_ok k41w23LowChart1_ok k41w23LowChart2_ok
  · exact checkedOfCharts k41w23HighChart0_ok k41w23HighChart1_ok k41w23HighChart2_ok

theorem slab41_ok : SlabChecked 41 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k41w23LowChart0_ok k41w23LowChart1_ok k41w23LowChart2_ok
  · exact checkedOfCharts k41w23HighChart0_ok k41w23HighChart1_ok k41w23HighChart2_ok
  · exact checkedOfCharts k42w23LowChart0_ok k42w23LowChart1_ok k42w23LowChart2_ok
  · exact checkedOfCharts k42w23HighChart0_ok k42w23HighChart1_ok k42w23HighChart2_ok

theorem slab42_ok : SlabChecked 42 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k42w23LowChart0_ok k42w23LowChart1_ok k42w23LowChart2_ok
  · exact checkedOfCharts k42w23HighChart0_ok k42w23HighChart1_ok k42w23HighChart2_ok
  · exact checkedOfCharts k43w23LowChart0_ok k43w23LowChart1_ok k43w23LowChart2_ok
  · exact checkedOfCharts k43w23HighChart0_ok k43w23HighChart1_ok k43w23HighChart2_ok

theorem slab43_ok : SlabChecked 43 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k43w23LowChart0_ok k43w23LowChart1_ok k43w23LowChart2_ok
  · exact checkedOfCharts k43w23HighChart0_ok k43w23HighChart1_ok k43w23HighChart2_ok
  · exact checkedOfCharts k44w23LowChart0_ok k44w23LowChart1_ok k44w23LowChart2_ok
  · exact checkedOfCharts k44w23HighChart0_ok k44w23HighChart1_ok k44w23HighChart2_ok

theorem slab44_ok : SlabChecked 44 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k44w23LowChart0_ok k44w23LowChart1_ok k44w23LowChart2_ok
  · exact checkedOfCharts k44w23HighChart0_ok k44w23HighChart1_ok k44w23HighChart2_ok
  · exact checkedOfCharts k45w23LowChart0_ok k45w23LowChart1_ok k45w23LowChart2_ok
  · exact checkedOfCharts k45w23HighChart0_ok k45w23HighChart1_ok k45w23HighChart2_ok

theorem slab45_ok : SlabChecked 45 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k45w23LowChart0_ok k45w23LowChart1_ok k45w23LowChart2_ok
  · exact checkedOfCharts k45w23HighChart0_ok k45w23HighChart1_ok k45w23HighChart2_ok
  · exact checkedOfCharts k46w23LowChart0_ok k46w23LowChart1_ok k46w23LowChart2_ok
  · exact checkedOfCharts k46w23HighChart0_ok k46w23HighChart1_ok k46w23HighChart2_ok

theorem slab46_ok : SlabChecked 46 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k46w23LowChart0_ok k46w23LowChart1_ok k46w23LowChart2_ok
  · exact checkedOfCharts k46w23HighChart0_ok k46w23HighChart1_ok k46w23HighChart2_ok
  · exact checkedOfCharts k47w23LowChart0_ok k47w23LowChart1_ok k47w23LowChart2_ok
  · exact checkedOfCharts k47w23HighChart0_ok k47w23HighChart1_ok k47w23HighChart2_ok

theorem slab47_ok : SlabChecked 47 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k47w23LowChart0_ok k47w23LowChart1_ok k47w23LowChart2_ok
  · exact checkedOfCharts k47w23HighChart0_ok k47w23HighChart1_ok k47w23HighChart2_ok
  · exact checkedOfCharts k48w23LowChart0_ok k48w23LowChart1_ok k48w23LowChart2_ok
  · exact checkedOfCharts k48w23HighChart0_ok k48w23HighChart1_ok k48w23HighChart2_ok

theorem slab48_ok : SlabChecked 48 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k48w23LowChart0_ok k48w23LowChart1_ok k48w23LowChart2_ok
  · exact checkedOfCharts k48w23HighChart0_ok k48w23HighChart1_ok k48w23HighChart2_ok
  · exact checkedOfCharts k49w23LowChart0_ok k49w23LowChart1_ok k49w23LowChart2_ok
  · exact checkedOfCharts k49w23HighChart0_ok k49w23HighChart1_ok k49w23HighChart2_ok

theorem slab49_ok : SlabChecked 49 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k49w23LowChart0_ok k49w23LowChart1_ok k49w23LowChart2_ok
  · exact checkedOfCharts k49w23HighChart0_ok k49w23HighChart1_ok k49w23HighChart2_ok
  · exact checkedOfCharts k50w23LowChart0_ok k50w23LowChart1_ok k50w23LowChart2_ok
  · exact checkedOfCharts k50w23HighChart0_ok k50w23HighChart1_ok k50w23HighChart2_ok

theorem slab50_ok : SlabChecked 50 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k50w23LowChart0_ok k50w23LowChart1_ok k50w23LowChart2_ok
  · exact checkedOfCharts k50w23HighChart0_ok k50w23HighChart1_ok k50w23HighChart2_ok
  · exact checkedOfCharts k51w23LowChart0_ok k51w23LowChart1_ok k51w23LowChart2_ok
  · exact checkedOfCharts k51w23HighChart0_ok k51w23HighChart1_ok k51w23HighChart2_ok

theorem slab51_ok : SlabChecked 51 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k51w23LowChart0_ok k51w23LowChart1_ok k51w23LowChart2_ok
  · exact checkedOfCharts k51w23HighChart0_ok k51w23HighChart1_ok k51w23HighChart2_ok
  · exact checkedOfCharts k52w23LowChart0_ok k52w23LowChart1_ok k52w23LowChart2_ok
  · exact checkedOfCharts k52w23HighChart0_ok k52w23HighChart1_ok k52w23HighChart2_ok

theorem slab52_ok : SlabChecked 52 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k52w23LowChart0_ok k52w23LowChart1_ok k52w23LowChart2_ok
  · exact checkedOfCharts k52w23HighChart0_ok k52w23HighChart1_ok k52w23HighChart2_ok
  · exact checkedOfCharts k53w23LowChart0_ok k53w23LowChart1_ok k53w23LowChart2_ok
  · exact checkedOfCharts k53w23HighChart0_ok k53w23HighChart1_ok k53w23HighChart2_ok

theorem slab53_ok : SlabChecked 53 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k53w23LowChart0_ok k53w23LowChart1_ok k53w23LowChart2_ok
  · exact checkedOfCharts k53w23HighChart0_ok k53w23HighChart1_ok k53w23HighChart2_ok
  · exact checkedOfCharts k54w23LowChart0_ok k54w23LowChart1_ok k54w23LowChart2_ok
  · exact checkedOfCharts k54w23HighChart0_ok k54w23HighChart1_ok k54w23HighChart2_ok

theorem slab54_ok : SlabChecked 54 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k54w23LowChart0_ok k54w23LowChart1_ok k54w23LowChart2_ok
  · exact checkedOfCharts k54w23HighChart0_ok k54w23HighChart1_ok k54w23HighChart2_ok
  · exact checkedOfCharts k55w23LowChart0_ok k55w23LowChart1_ok k55w23LowChart2_ok
  · exact checkedOfCharts k55w23HighChart0_ok k55w23HighChart1_ok k55w23HighChart2_ok

theorem slab55_ok : SlabChecked 55 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k55w23LowChart0_ok k55w23LowChart1_ok k55w23LowChart2_ok
  · exact checkedOfCharts k55w23HighChart0_ok k55w23HighChart1_ok k55w23HighChart2_ok
  · exact checkedOfCharts k56w23LowChart0_ok k56w23LowChart1_ok k56w23LowChart2_ok
  · exact checkedOfCharts k56w23HighChart0_ok k56w23HighChart1_ok k56w23HighChart2_ok

theorem slab56_ok : SlabChecked 56 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k56w23LowChart0_ok k56w23LowChart1_ok k56w23LowChart2_ok
  · exact checkedOfCharts k56w23HighChart0_ok k56w23HighChart1_ok k56w23HighChart2_ok
  · exact checkedOfCharts k57w23LowChart0_ok k57w23LowChart1_ok k57w23LowChart2_ok
  · exact checkedOfCharts k57w23HighChart0_ok k57w23HighChart1_ok k57w23HighChart2_ok

theorem slab57_ok : SlabChecked 57 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k57w23LowChart0_ok k57w23LowChart1_ok k57w23LowChart2_ok
  · exact checkedOfCharts k57w23HighChart0_ok k57w23HighChart1_ok k57w23HighChart2_ok
  · exact checkedOfCharts k58w23LowChart0_ok k58w23LowChart1_ok k58w23LowChart2_ok
  · exact checkedOfCharts k58w23HighChart0_ok k58w23HighChart1_ok k58w23HighChart2_ok

theorem slab58_ok : SlabChecked 58 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k58w23LowChart0_ok k58w23LowChart1_ok k58w23LowChart2_ok
  · exact checkedOfCharts k58w23HighChart0_ok k58w23HighChart1_ok k58w23HighChart2_ok
  · exact checkedOfCharts k59w23LowChart0_ok k59w23LowChart1_ok k59w23LowChart2_ok
  · exact checkedOfCharts k59w23HighChart0_ok k59w23HighChart1_ok k59w23HighChart2_ok

theorem slab59_ok : SlabChecked 59 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k59w23LowChart0_ok k59w23LowChart1_ok k59w23LowChart2_ok
  · exact checkedOfCharts k59w23HighChart0_ok k59w23HighChart1_ok k59w23HighChart2_ok
  · exact checkedOfCharts k60w23LowChart0_ok k60w23LowChart1_ok k60w23LowChart2_ok
  · exact checkedOfCharts k60w23HighChart0_ok k60w23HighChart1_ok k60w23HighChart2_ok

theorem slab60_ok : SlabChecked 60 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k60w23LowChart0_ok k60w23LowChart1_ok k60w23LowChart2_ok
  · exact checkedOfCharts k60w23HighChart0_ok k60w23HighChart1_ok k60w23HighChart2_ok
  · exact checkedOfCharts k61w23LowChart0_ok k61w23LowChart1_ok k61w23LowChart2_ok
  · exact checkedOfCharts k61w23HighChart0_ok k61w23HighChart1_ok k61w23HighChart2_ok

theorem slab61_ok : SlabChecked 61 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k61w23LowChart0_ok k61w23LowChart1_ok k61w23LowChart2_ok
  · exact checkedOfCharts k61w23HighChart0_ok k61w23HighChart1_ok k61w23HighChart2_ok
  · exact checkedOfCharts k62w23LowChart0_ok k62w23LowChart1_ok k62w23LowChart2_ok
  · exact checkedOfCharts k62w23HighChart0_ok k62w23HighChart1_ok k62w23HighChart2_ok

theorem slab62_ok : SlabChecked 62 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k62w23LowChart0_ok k62w23LowChart1_ok k62w23LowChart2_ok
  · exact checkedOfCharts k62w23HighChart0_ok k62w23HighChart1_ok k62w23HighChart2_ok
  · exact checkedOfCharts k63w23LowChart0_ok k63w23LowChart1_ok k63w23LowChart2_ok
  · exact checkedOfCharts k63w23HighChart0_ok k63w23HighChart1_ok k63w23HighChart2_ok

theorem slab63_ok : SlabChecked 63 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k63w23LowChart0_ok k63w23LowChart1_ok k63w23LowChart2_ok
  · exact checkedOfCharts k63w23HighChart0_ok k63w23HighChart1_ok k63w23HighChart2_ok
  · exact checkedOfCharts k64w23LowChart0_ok k64w23LowChart1_ok k64w23LowChart2_ok
  · exact checkedOfCharts k64w23HighChart0_ok k64w23HighChart1_ok k64w23HighChart2_ok

theorem slab64_ok : SlabChecked 64 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k64w23LowChart0_ok k64w23LowChart1_ok k64w23LowChart2_ok
  · exact checkedOfCharts k64w23HighChart0_ok k64w23HighChart1_ok k64w23HighChart2_ok
  · exact checkedOfCharts k65w23LowChart0_ok k65w23LowChart1_ok k65w23LowChart2_ok
  · exact checkedOfCharts k65w23HighChart0_ok k65w23HighChart1_ok k65w23HighChart2_ok

theorem slab65_ok : SlabChecked 65 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k65w23LowChart0_ok k65w23LowChart1_ok k65w23LowChart2_ok
  · exact checkedOfCharts k65w23HighChart0_ok k65w23HighChart1_ok k65w23HighChart2_ok
  · exact checkedOfCharts k66w23LowChart0_ok k66w23LowChart1_ok k66w23LowChart2_ok
  · exact checkedOfCharts k66w23HighChart0_ok k66w23HighChart1_ok k66w23HighChart2_ok

theorem slab66_ok : SlabChecked 66 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k66w23LowChart0_ok k66w23LowChart1_ok k66w23LowChart2_ok
  · exact checkedOfCharts k66w23HighChart0_ok k66w23HighChart1_ok k66w23HighChart2_ok
  · exact checkedOfCharts k67w23LowChart0_ok k67w23LowChart1_ok k67w23LowChart2_ok
  · exact checkedOfCharts k67w23HighChart0_ok k67w23HighChart1_ok k67w23HighChart2_ok

theorem slab67_ok : SlabChecked 67 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k67w23LowChart0_ok k67w23LowChart1_ok k67w23LowChart2_ok
  · exact checkedOfCharts k67w23HighChart0_ok k67w23HighChart1_ok k67w23HighChart2_ok
  · exact checkedOfCharts k68w23LowChart0_ok k68w23LowChart1_ok k68w23LowChart2_ok
  · exact checkedOfCharts k68w23HighChart0_ok k68w23HighChart1_ok k68w23HighChart2_ok

theorem slab68_ok : SlabChecked 68 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k68w23LowChart0_ok k68w23LowChart1_ok k68w23LowChart2_ok
  · exact checkedOfCharts k68w23HighChart0_ok k68w23HighChart1_ok k68w23HighChart2_ok
  · exact checkedOfCharts k69w23LowChart0_ok k69w23LowChart1_ok k69w23LowChart2_ok
  · exact checkedOfCharts k69w23HighChart0_ok k69w23HighChart1_ok k69w23HighChart2_ok

theorem slab69_ok : SlabChecked 69 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k69w23LowChart0_ok k69w23LowChart1_ok k69w23LowChart2_ok
  · exact checkedOfCharts k69w23HighChart0_ok k69w23HighChart1_ok k69w23HighChart2_ok
  · exact checkedOfCharts k70w23LowChart0_ok k70w23LowChart1_ok k70w23LowChart2_ok
  · exact checkedOfCharts k70w23HighChart0_ok k70w23HighChart1_ok k70w23HighChart2_ok

theorem slab70_ok : SlabChecked 70 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k70w23LowChart0_ok k70w23LowChart1_ok k70w23LowChart2_ok
  · exact checkedOfCharts k70w23HighChart0_ok k70w23HighChart1_ok k70w23HighChart2_ok
  · exact checkedOfCharts k71w23LowChart0_ok k71w23LowChart1_ok k71w23LowChart2_ok
  · exact checkedOfCharts k71w23HighChart0_ok k71w23HighChart1_ok k71w23HighChart2_ok

theorem slab71_ok : SlabChecked 71 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k71w23LowChart0_ok k71w23LowChart1_ok k71w23LowChart2_ok
  · exact checkedOfCharts k71w23HighChart0_ok k71w23HighChart1_ok k71w23HighChart2_ok
  · exact checkedOfCharts k72w23LowChart0_ok k72w23LowChart1_ok k72w23LowChart2_ok
  · exact checkedOfCharts k72w23HighChart0_ok k72w23HighChart1_ok k72w23HighChart2_ok

theorem slab72_ok : SlabChecked 72 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k72w23LowChart0_ok k72w23LowChart1_ok k72w23LowChart2_ok
  · exact checkedOfCharts k72w23HighChart0_ok k72w23HighChart1_ok k72w23HighChart2_ok
  · exact checkedOfCharts k73w23LowChart0_ok k73w23LowChart1_ok k73w23LowChart2_ok
  · exact checkedOfCharts k73w23HighChart0_ok k73w23HighChart1_ok k73w23HighChart2_ok

theorem slab73_ok : SlabChecked 73 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k73w23LowChart0_ok k73w23LowChart1_ok k73w23LowChart2_ok
  · exact checkedOfCharts k73w23HighChart0_ok k73w23HighChart1_ok k73w23HighChart2_ok
  · exact checkedOfCharts k74w23LowChart0_ok k74w23LowChart1_ok k74w23LowChart2_ok
  · exact checkedOfCharts k74w23HighChart0_ok k74w23HighChart1_ok k74w23HighChart2_ok

theorem slab74_ok : SlabChecked 74 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k74w23LowChart0_ok k74w23LowChart1_ok k74w23LowChart2_ok
  · exact checkedOfCharts k74w23HighChart0_ok k74w23HighChart1_ok k74w23HighChart2_ok
  · exact checkedOfCharts k75w23LowChart0_ok k75w23LowChart1_ok k75w23LowChart2_ok
  · exact checkedOfCharts k75w23HighChart0_ok k75w23HighChart1_ok k75w23HighChart2_ok

theorem slab75_ok : SlabChecked 75 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k75w23LowChart0_ok k75w23LowChart1_ok k75w23LowChart2_ok
  · exact checkedOfCharts k75w23HighChart0_ok k75w23HighChart1_ok k75w23HighChart2_ok
  · exact checkedOfCharts k76w23LowChart0_ok k76w23LowChart1_ok k76w23LowChart2_ok
  · exact checkedOfCharts k76w23HighChart0_ok k76w23HighChart1_ok k76w23HighChart2_ok

theorem slab76_ok : SlabChecked 76 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k76w23LowChart0_ok k76w23LowChart1_ok k76w23LowChart2_ok
  · exact checkedOfCharts k76w23HighChart0_ok k76w23HighChart1_ok k76w23HighChart2_ok
  · exact checkedOfCharts k77w23LowChart0_ok k77w23LowChart1_ok k77w23LowChart2_ok
  · exact checkedOfCharts k77w23HighChart0_ok k77w23HighChart1_ok k77w23HighChart2_ok

theorem slab77_ok : SlabChecked 77 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k77w23LowChart0_ok k77w23LowChart1_ok k77w23LowChart2_ok
  · exact checkedOfCharts k77w23HighChart0_ok k77w23HighChart1_ok k77w23HighChart2_ok
  · exact checkedOfCharts k78w23LowChart0_ok k78w23LowChart1_ok k78w23LowChart2_ok
  · exact checkedOfCharts k78w23HighChart0_ok k78w23HighChart1_ok k78w23HighChart2_ok

end HlawkaSchatten.BelowExponent.FSlabCheck
