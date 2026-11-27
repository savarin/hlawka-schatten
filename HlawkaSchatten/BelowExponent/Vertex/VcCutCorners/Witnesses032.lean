/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees032

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses032`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP032_outer : vcCutP032.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP032_roots vcCutP032_bounds_eq vcCutP032_trees_ok

theorem vcCutP033_outer : vcCutP033.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP033_roots vcCutP033_bounds_eq vcCutP033_trees_ok

theorem vcCutP034_outer : vcCutP034.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP034_roots vcCutP034_bounds_eq vcCutP034_trees_ok

theorem vcCutP035_outer : vcCutP035.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP035_roots vcCutP035_bounds_eq vcCutP035_trees_ok

theorem vcCutP036_outer : vcCutP036.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP036_roots vcCutP036_bounds_eq vcCutP036_trees_ok

theorem vcCutP037_outer : vcCutP037.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP037_roots vcCutP037_bounds_eq vcCutP037_trees_ok

theorem vcCutP038_outer : vcCutP038.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP038_roots vcCutP038_bounds_eq vcCutP038_trees_ok

theorem vcCutP039_outer : vcCutP039.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP039_roots vcCutP039_bounds_eq vcCutP039_trees_ok

theorem vcCutP040_outer : vcCutP040.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP040_roots vcCutP040_bounds_eq vcCutP040_trees_ok

theorem vcCutP041_outer : vcCutP041.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP041_roots vcCutP041_bounds_eq vcCutP041_trees_ok

theorem vcCutP042_outer : vcCutP042.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP042_roots vcCutP042_bounds_eq vcCutP042_trees_ok

theorem vcCutP043_outer : vcCutP043.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP043_roots vcCutP043_bounds_eq vcCutP043_trees_ok

theorem vcCutP044_outer : vcCutP044.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP044_roots vcCutP044_bounds_eq vcCutP044_trees_ok

theorem vcCutP045_outer : vcCutP045.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP045_roots vcCutP045_bounds_eq vcCutP045_trees_ok

theorem vcCutP046_outer : vcCutP046.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP046_roots vcCutP046_bounds_eq vcCutP046_trees_ok

theorem vcCutP047_outer : vcCutP047.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP047_roots vcCutP047_bounds_eq vcCutP047_trees_ok

theorem vcCutP048_outer : vcCutP048.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP048_roots vcCutP048_bounds_eq vcCutP048_trees_ok

theorem vcCutP049_outer : vcCutP049.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP049_roots vcCutP049_bounds_eq vcCutP049_trees_ok

theorem vcCutP050_outer : vcCutP050.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP050_roots vcCutP050_bounds_eq vcCutP050_trees_ok

theorem vcCutP051_outer : vcCutP051.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP051_roots vcCutP051_bounds_eq vcCutP051_trees_ok

theorem vcCutP052_outer : vcCutP052.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP052_roots vcCutP052_bounds_eq vcCutP052_trees_ok

theorem vcCutP053_outer : vcCutP053.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP053_roots vcCutP053_bounds_eq vcCutP053_trees_ok

theorem vcCutP054_outer : vcCutP054.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP054_roots vcCutP054_bounds_eq vcCutP054_trees_ok

theorem vcCutP055_outer : vcCutP055.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP055_roots vcCutP055_bounds_eq vcCutP055_trees_ok

theorem vcCutP056_outer : vcCutP056.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP056_roots vcCutP056_bounds_eq vcCutP056_trees_ok

theorem vcCutP057_outer : vcCutP057.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP057_roots vcCutP057_bounds_eq vcCutP057_trees_ok

theorem vcCutP058_outer : vcCutP058.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP058_roots vcCutP058_bounds_eq vcCutP058_trees_ok

theorem vcCutP059_outer : vcCutP059.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP059_roots vcCutP059_bounds_eq vcCutP059_trees_ok

theorem vcCutP060_outer : vcCutP060.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP060_roots vcCutP060_bounds_eq vcCutP060_trees_ok

theorem vcCutP061_outer : vcCutP061.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP061_roots vcCutP061_bounds_eq vcCutP061_trees_ok

theorem vcCutP062_outer : vcCutP062.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP062_roots vcCutP062_bounds_eq vcCutP062_trees_ok

theorem vcCutP063_outer : vcCutP063.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP063_roots vcCutP063_bounds_eq vcCutP063_trees_ok

theorem vcCutWitnesses032 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints032.toList :=
  ⟨vcCutP032_outer,
   vcCutP033_outer,
   vcCutP034_outer,
   vcCutP035_outer,
   vcCutP036_outer,
   vcCutP037_outer,
   vcCutP038_outer,
   vcCutP039_outer,
   vcCutP040_outer,
   vcCutP041_outer,
   vcCutP042_outer,
   vcCutP043_outer,
   vcCutP044_outer,
   vcCutP045_outer,
   vcCutP046_outer,
   vcCutP047_outer,
   vcCutP048_outer,
   vcCutP049_outer,
   vcCutP050_outer,
   vcCutP051_outer,
   vcCutP052_outer,
   vcCutP053_outer,
   vcCutP054_outer,
   vcCutP055_outer,
   vcCutP056_outer,
   vcCutP057_outer,
   vcCutP058_outer,
   vcCutP059_outer,
   vcCutP060_outer,
   vcCutP061_outer,
   vcCutP062_outer,
   vcCutP063_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
