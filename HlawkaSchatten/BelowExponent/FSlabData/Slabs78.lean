/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabSchedule
public import HlawkaSchatten.BelowExponent.FSlabData.Knot78Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot79Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot80Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot81Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot82Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot83Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot84Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot85Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot86Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot87Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot88Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot89Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot90Weight23
public import HlawkaSchatten.BelowExponent.FSlabData.Knot90Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot91Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot92Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot93Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot94Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot95Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot96Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot97Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot98Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot99Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot100Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot101Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot102Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot103Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot104Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot105Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot106Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot107Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot108Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot109Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot110Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot111Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot112Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot113Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot114Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot115Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot116Weight25
public import HlawkaSchatten.BelowExponent.FSlabData.Knot117Weight25

/-! Exact data for the weighted F-slab facet checks: `Slabs78`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public section

namespace HlawkaSchatten.BelowExponent.FSlabCheck

theorem slab78_ok : SlabChecked 78 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k78w23LowChart0_ok k78w23LowChart1_ok k78w23LowChart2_ok
  · exact checkedOfCharts k78w23HighChart0_ok k78w23HighChart1_ok k78w23HighChart2_ok
  · exact checkedOfCharts k79w23LowChart0_ok k79w23LowChart1_ok k79w23LowChart2_ok
  · exact checkedOfCharts k79w23HighChart0_ok k79w23HighChart1_ok k79w23HighChart2_ok

theorem slab79_ok : SlabChecked 79 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k79w23LowChart0_ok k79w23LowChart1_ok k79w23LowChart2_ok
  · exact checkedOfCharts k79w23HighChart0_ok k79w23HighChart1_ok k79w23HighChart2_ok
  · exact checkedOfCharts k80w23LowChart0_ok k80w23LowChart1_ok k80w23LowChart2_ok
  · exact checkedOfCharts k80w23HighChart0_ok k80w23HighChart1_ok k80w23HighChart2_ok

theorem slab80_ok : SlabChecked 80 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k80w23LowChart0_ok k80w23LowChart1_ok k80w23LowChart2_ok
  · exact checkedOfCharts k80w23HighChart0_ok k80w23HighChart1_ok k80w23HighChart2_ok
  · exact checkedOfCharts k81w23LowChart0_ok k81w23LowChart1_ok k81w23LowChart2_ok
  · exact checkedOfCharts k81w23HighChart0_ok k81w23HighChart1_ok k81w23HighChart2_ok

theorem slab81_ok : SlabChecked 81 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k81w23LowChart0_ok k81w23LowChart1_ok k81w23LowChart2_ok
  · exact checkedOfCharts k81w23HighChart0_ok k81w23HighChart1_ok k81w23HighChart2_ok
  · exact checkedOfCharts k82w23LowChart0_ok k82w23LowChart1_ok k82w23LowChart2_ok
  · exact checkedOfCharts k82w23HighChart0_ok k82w23HighChart1_ok k82w23HighChart2_ok

theorem slab82_ok : SlabChecked 82 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k82w23LowChart0_ok k82w23LowChart1_ok k82w23LowChart2_ok
  · exact checkedOfCharts k82w23HighChart0_ok k82w23HighChart1_ok k82w23HighChart2_ok
  · exact checkedOfCharts k83w23LowChart0_ok k83w23LowChart1_ok k83w23LowChart2_ok
  · exact checkedOfCharts k83w23HighChart0_ok k83w23HighChart1_ok k83w23HighChart2_ok

theorem slab83_ok : SlabChecked 83 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k83w23LowChart0_ok k83w23LowChart1_ok k83w23LowChart2_ok
  · exact checkedOfCharts k83w23HighChart0_ok k83w23HighChart1_ok k83w23HighChart2_ok
  · exact checkedOfCharts k84w23LowChart0_ok k84w23LowChart1_ok k84w23LowChart2_ok
  · exact checkedOfCharts k84w23HighChart0_ok k84w23HighChart1_ok k84w23HighChart2_ok

theorem slab84_ok : SlabChecked 84 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k84w23LowChart0_ok k84w23LowChart1_ok k84w23LowChart2_ok
  · exact checkedOfCharts k84w23HighChart0_ok k84w23HighChart1_ok k84w23HighChart2_ok
  · exact checkedOfCharts k85w23LowChart0_ok k85w23LowChart1_ok k85w23LowChart2_ok
  · exact checkedOfCharts k85w23HighChart0_ok k85w23HighChart1_ok k85w23HighChart2_ok

theorem slab85_ok : SlabChecked 85 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k85w23LowChart0_ok k85w23LowChart1_ok k85w23LowChart2_ok
  · exact checkedOfCharts k85w23HighChart0_ok k85w23HighChart1_ok k85w23HighChart2_ok
  · exact checkedOfCharts k86w23LowChart0_ok k86w23LowChart1_ok k86w23LowChart2_ok
  · exact checkedOfCharts k86w23HighChart0_ok k86w23HighChart1_ok k86w23HighChart2_ok

theorem slab86_ok : SlabChecked 86 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k86w23LowChart0_ok k86w23LowChart1_ok k86w23LowChart2_ok
  · exact checkedOfCharts k86w23HighChart0_ok k86w23HighChart1_ok k86w23HighChart2_ok
  · exact checkedOfCharts k87w23LowChart0_ok k87w23LowChart1_ok k87w23LowChart2_ok
  · exact checkedOfCharts k87w23HighChart0_ok k87w23HighChart1_ok k87w23HighChart2_ok

theorem slab87_ok : SlabChecked 87 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k87w23LowChart0_ok k87w23LowChart1_ok k87w23LowChart2_ok
  · exact checkedOfCharts k87w23HighChart0_ok k87w23HighChart1_ok k87w23HighChart2_ok
  · exact checkedOfCharts k88w23LowChart0_ok k88w23LowChart1_ok k88w23LowChart2_ok
  · exact checkedOfCharts k88w23HighChart0_ok k88w23HighChart1_ok k88w23HighChart2_ok

theorem slab88_ok : SlabChecked 88 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k88w23LowChart0_ok k88w23LowChart1_ok k88w23LowChart2_ok
  · exact checkedOfCharts k88w23HighChart0_ok k88w23HighChart1_ok k88w23HighChart2_ok
  · exact checkedOfCharts k89w23LowChart0_ok k89w23LowChart1_ok k89w23LowChart2_ok
  · exact checkedOfCharts k89w23HighChart0_ok k89w23HighChart1_ok k89w23HighChart2_ok

theorem slab89_ok : SlabChecked 89 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k89w23LowChart0_ok k89w23LowChart1_ok k89w23LowChart2_ok
  · exact checkedOfCharts k89w23HighChart0_ok k89w23HighChart1_ok k89w23HighChart2_ok
  · exact checkedOfCharts k90w23LowChart0_ok k90w23LowChart1_ok k90w23LowChart2_ok
  · exact checkedOfCharts k90w23HighChart0_ok k90w23HighChart1_ok k90w23HighChart2_ok

theorem slab90_ok : SlabChecked 90 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k90w25LowChart0_ok k90w25LowChart1_ok k90w25LowChart2_ok
  · exact checkedOfCharts k90w25HighChart0_ok k90w25HighChart1_ok k90w25HighChart2_ok
  · exact checkedOfCharts k91w25LowChart0_ok k91w25LowChart1_ok k91w25LowChart2_ok
  · exact checkedOfCharts k91w25HighChart0_ok k91w25HighChart1_ok k91w25HighChart2_ok

theorem slab91_ok : SlabChecked 91 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k91w25LowChart0_ok k91w25LowChart1_ok k91w25LowChart2_ok
  · exact checkedOfCharts k91w25HighChart0_ok k91w25HighChart1_ok k91w25HighChart2_ok
  · exact checkedOfCharts k92w25LowChart0_ok k92w25LowChart1_ok k92w25LowChart2_ok
  · exact checkedOfCharts k92w25HighChart0_ok k92w25HighChart1_ok k92w25HighChart2_ok

theorem slab92_ok : SlabChecked 92 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k92w25LowChart0_ok k92w25LowChart1_ok k92w25LowChart2_ok
  · exact checkedOfCharts k92w25HighChart0_ok k92w25HighChart1_ok k92w25HighChart2_ok
  · exact checkedOfCharts k93w25LowChart0_ok k93w25LowChart1_ok k93w25LowChart2_ok
  · exact checkedOfCharts k93w25HighChart0_ok k93w25HighChart1_ok k93w25HighChart2_ok

theorem slab93_ok : SlabChecked 93 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k93w25LowChart0_ok k93w25LowChart1_ok k93w25LowChart2_ok
  · exact checkedOfCharts k93w25HighChart0_ok k93w25HighChart1_ok k93w25HighChart2_ok
  · exact checkedOfCharts k94w25LowChart0_ok k94w25LowChart1_ok k94w25LowChart2_ok
  · exact checkedOfCharts k94w25HighChart0_ok k94w25HighChart1_ok k94w25HighChart2_ok

theorem slab94_ok : SlabChecked 94 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k94w25LowChart0_ok k94w25LowChart1_ok k94w25LowChart2_ok
  · exact checkedOfCharts k94w25HighChart0_ok k94w25HighChart1_ok k94w25HighChart2_ok
  · exact checkedOfCharts k95w25LowChart0_ok k95w25LowChart1_ok k95w25LowChart2_ok
  · exact checkedOfCharts k95w25HighChart0_ok k95w25HighChart1_ok k95w25HighChart2_ok

theorem slab95_ok : SlabChecked 95 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k95w25LowChart0_ok k95w25LowChart1_ok k95w25LowChart2_ok
  · exact checkedOfCharts k95w25HighChart0_ok k95w25HighChart1_ok k95w25HighChart2_ok
  · exact checkedOfCharts k96w25LowChart0_ok k96w25LowChart1_ok k96w25LowChart2_ok
  · exact checkedOfCharts k96w25HighChart0_ok k96w25HighChart1_ok k96w25HighChart2_ok

theorem slab96_ok : SlabChecked 96 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k96w25LowChart0_ok k96w25LowChart1_ok k96w25LowChart2_ok
  · exact checkedOfCharts k96w25HighChart0_ok k96w25HighChart1_ok k96w25HighChart2_ok
  · exact checkedOfCharts k97w25LowChart0_ok k97w25LowChart1_ok k97w25LowChart2_ok
  · exact checkedOfCharts k97w25HighChart0_ok k97w25HighChart1_ok k97w25HighChart2_ok

theorem slab97_ok : SlabChecked 97 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k97w25LowChart0_ok k97w25LowChart1_ok k97w25LowChart2_ok
  · exact checkedOfCharts k97w25HighChart0_ok k97w25HighChart1_ok k97w25HighChart2_ok
  · exact checkedOfCharts k98w25LowChart0_ok k98w25LowChart1_ok k98w25LowChart2_ok
  · exact checkedOfCharts k98w25HighChart0_ok k98w25HighChart1_ok k98w25HighChart2_ok

theorem slab98_ok : SlabChecked 98 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k98w25LowChart0_ok k98w25LowChart1_ok k98w25LowChart2_ok
  · exact checkedOfCharts k98w25HighChart0_ok k98w25HighChart1_ok k98w25HighChart2_ok
  · exact checkedOfCharts k99w25LowChart0_ok k99w25LowChart1_ok k99w25LowChart2_ok
  · exact checkedOfCharts k99w25HighChart0_ok k99w25HighChart1_ok k99w25HighChart2_ok

theorem slab99_ok : SlabChecked 99 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k99w25LowChart0_ok k99w25LowChart1_ok k99w25LowChart2_ok
  · exact checkedOfCharts k99w25HighChart0_ok k99w25HighChart1_ok k99w25HighChart2_ok
  · exact checkedOfCharts k100w25LowChart0_ok k100w25LowChart1_ok k100w25LowChart2_ok
  · exact checkedOfCharts k100w25HighChart0_ok k100w25HighChart1_ok k100w25HighChart2_ok

theorem slab100_ok : SlabChecked 100 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k100w25LowChart0_ok k100w25LowChart1_ok k100w25LowChart2_ok
  · exact checkedOfCharts k100w25HighChart0_ok k100w25HighChart1_ok k100w25HighChart2_ok
  · exact checkedOfCharts k101w25LowChart0_ok k101w25LowChart1_ok k101w25LowChart2_ok
  · exact checkedOfCharts k101w25HighChart0_ok k101w25HighChart1_ok k101w25HighChart2_ok

theorem slab101_ok : SlabChecked 101 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k101w25LowChart0_ok k101w25LowChart1_ok k101w25LowChart2_ok
  · exact checkedOfCharts k101w25HighChart0_ok k101w25HighChart1_ok k101w25HighChart2_ok
  · exact checkedOfCharts k102w25LowChart0_ok k102w25LowChart1_ok k102w25LowChart2_ok
  · exact checkedOfCharts k102w25HighChart0_ok k102w25HighChart1_ok k102w25HighChart2_ok

theorem slab102_ok : SlabChecked 102 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k102w25LowChart0_ok k102w25LowChart1_ok k102w25LowChart2_ok
  · exact checkedOfCharts k102w25HighChart0_ok k102w25HighChart1_ok k102w25HighChart2_ok
  · exact checkedOfCharts k103w25LowChart0_ok k103w25LowChart1_ok k103w25LowChart2_ok
  · exact checkedOfCharts k103w25HighChart0_ok k103w25HighChart1_ok k103w25HighChart2_ok

theorem slab103_ok : SlabChecked 103 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k103w25LowChart0_ok k103w25LowChart1_ok k103w25LowChart2_ok
  · exact checkedOfCharts k103w25HighChart0_ok k103w25HighChart1_ok k103w25HighChart2_ok
  · exact checkedOfCharts k104w25LowChart0_ok k104w25LowChart1_ok k104w25LowChart2_ok
  · exact checkedOfCharts k104w25HighChart0_ok k104w25HighChart1_ok k104w25HighChart2_ok

theorem slab104_ok : SlabChecked 104 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k104w25LowChart0_ok k104w25LowChart1_ok k104w25LowChart2_ok
  · exact checkedOfCharts k104w25HighChart0_ok k104w25HighChart1_ok k104w25HighChart2_ok
  · exact checkedOfCharts k105w25LowChart0_ok k105w25LowChart1_ok k105w25LowChart2_ok
  · exact checkedOfCharts k105w25HighChart0_ok k105w25HighChart1_ok k105w25HighChart2_ok

theorem slab105_ok : SlabChecked 105 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k105w25LowChart0_ok k105w25LowChart1_ok k105w25LowChart2_ok
  · exact checkedOfCharts k105w25HighChart0_ok k105w25HighChart1_ok k105w25HighChart2_ok
  · exact checkedOfCharts k106w25LowChart0_ok k106w25LowChart1_ok k106w25LowChart2_ok
  · exact checkedOfCharts k106w25HighChart0_ok k106w25HighChart1_ok k106w25HighChart2_ok

theorem slab106_ok : SlabChecked 106 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k106w25LowChart0_ok k106w25LowChart1_ok k106w25LowChart2_ok
  · exact checkedOfCharts k106w25HighChart0_ok k106w25HighChart1_ok k106w25HighChart2_ok
  · exact checkedOfCharts k107w25LowChart0_ok k107w25LowChart1_ok k107w25LowChart2_ok
  · exact checkedOfCharts k107w25HighChart0_ok k107w25HighChart1_ok k107w25HighChart2_ok

theorem slab107_ok : SlabChecked 107 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k107w25LowChart0_ok k107w25LowChart1_ok k107w25LowChart2_ok
  · exact checkedOfCharts k107w25HighChart0_ok k107w25HighChart1_ok k107w25HighChart2_ok
  · exact checkedOfCharts k108w25LowChart0_ok k108w25LowChart1_ok k108w25LowChart2_ok
  · exact checkedOfCharts k108w25HighChart0_ok k108w25HighChart1_ok k108w25HighChart2_ok

theorem slab108_ok : SlabChecked 108 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k108w25LowChart0_ok k108w25LowChart1_ok k108w25LowChart2_ok
  · exact checkedOfCharts k108w25HighChart0_ok k108w25HighChart1_ok k108w25HighChart2_ok
  · exact checkedOfCharts k109w25LowChart0_ok k109w25LowChart1_ok k109w25LowChart2_ok
  · exact checkedOfCharts k109w25HighChart0_ok k109w25HighChart1_ok k109w25HighChart2_ok

theorem slab109_ok : SlabChecked 109 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k109w25LowChart0_ok k109w25LowChart1_ok k109w25LowChart2_ok
  · exact checkedOfCharts k109w25HighChart0_ok k109w25HighChart1_ok k109w25HighChart2_ok
  · exact checkedOfCharts k110w25LowChart0_ok k110w25LowChart1_ok k110w25LowChart2_ok
  · exact checkedOfCharts k110w25HighChart0_ok k110w25HighChart1_ok k110w25HighChart2_ok

theorem slab110_ok : SlabChecked 110 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k110w25LowChart0_ok k110w25LowChart1_ok k110w25LowChart2_ok
  · exact checkedOfCharts k110w25HighChart0_ok k110w25HighChart1_ok k110w25HighChart2_ok
  · exact checkedOfCharts k111w25LowChart0_ok k111w25LowChart1_ok k111w25LowChart2_ok
  · exact checkedOfCharts k111w25HighChart0_ok k111w25HighChart1_ok k111w25HighChart2_ok

theorem slab111_ok : SlabChecked 111 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k111w25LowChart0_ok k111w25LowChart1_ok k111w25LowChart2_ok
  · exact checkedOfCharts k111w25HighChart0_ok k111w25HighChart1_ok k111w25HighChart2_ok
  · exact checkedOfCharts k112w25LowChart0_ok k112w25LowChart1_ok k112w25LowChart2_ok
  · exact checkedOfCharts k112w25HighChart0_ok k112w25HighChart1_ok k112w25HighChart2_ok

theorem slab112_ok : SlabChecked 112 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k112w25LowChart0_ok k112w25LowChart1_ok k112w25LowChart2_ok
  · exact checkedOfCharts k112w25HighChart0_ok k112w25HighChart1_ok k112w25HighChart2_ok
  · exact checkedOfCharts k113w25LowChart0_ok k113w25LowChart1_ok k113w25LowChart2_ok
  · exact checkedOfCharts k113w25HighChart0_ok k113w25HighChart1_ok k113w25HighChart2_ok

theorem slab113_ok : SlabChecked 113 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k113w25LowChart0_ok k113w25LowChart1_ok k113w25LowChart2_ok
  · exact checkedOfCharts k113w25HighChart0_ok k113w25HighChart1_ok k113w25HighChart2_ok
  · exact checkedOfCharts k114w25LowChart0_ok k114w25LowChart1_ok k114w25LowChart2_ok
  · exact checkedOfCharts k114w25HighChart0_ok k114w25HighChart1_ok k114w25HighChart2_ok

theorem slab114_ok : SlabChecked 114 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k114w25LowChart0_ok k114w25LowChart1_ok k114w25LowChart2_ok
  · exact checkedOfCharts k114w25HighChart0_ok k114w25HighChart1_ok k114w25HighChart2_ok
  · exact checkedOfCharts k115w25LowChart0_ok k115w25LowChart1_ok k115w25LowChart2_ok
  · exact checkedOfCharts k115w25HighChart0_ok k115w25HighChart1_ok k115w25HighChart2_ok

theorem slab115_ok : SlabChecked 115 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k115w25LowChart0_ok k115w25LowChart1_ok k115w25LowChart2_ok
  · exact checkedOfCharts k115w25HighChart0_ok k115w25HighChart1_ok k115w25HighChart2_ok
  · exact checkedOfCharts k116w25LowChart0_ok k116w25LowChart1_ok k116w25LowChart2_ok
  · exact checkedOfCharts k116w25HighChart0_ok k116w25HighChart1_ok k116w25HighChart2_ok

theorem slab116_ok : SlabChecked 116 := by
  intro cap side
  cases cap <;> cases side
  · exact checkedOfCharts k116w25LowChart0_ok k116w25LowChart1_ok k116w25LowChart2_ok
  · exact checkedOfCharts k116w25HighChart0_ok k116w25HighChart1_ok k116w25HighChart2_ok
  · exact checkedOfCharts k117w25LowChart0_ok k117w25LowChart1_ok k117w25LowChart2_ok
  · exact checkedOfCharts k117w25HighChart0_ok k117w25HighChart1_ok k117w25HighChart2_ok

end HlawkaSchatten.BelowExponent.FSlabCheck
