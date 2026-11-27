/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees800

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses800`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP800_outer : vcCutP800.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP800_roots vcCutP800_bounds_eq vcCutP800_trees_ok

theorem vcCutP801_outer : vcCutP801.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP801_roots vcCutP801_bounds_eq vcCutP801_trees_ok

theorem vcCutP802_outer : vcCutP802.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP802_roots vcCutP802_bounds_eq vcCutP802_trees_ok

theorem vcCutP803_outer : vcCutP803.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP803_roots vcCutP803_bounds_eq vcCutP803_trees_ok

theorem vcCutP804_outer : vcCutP804.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP804_roots vcCutP804_bounds_eq vcCutP804_trees_ok

theorem vcCutP805_outer : vcCutP805.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP805_roots vcCutP805_bounds_eq vcCutP805_trees_ok

theorem vcCutP806_outer : vcCutP806.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP806_roots vcCutP806_bounds_eq vcCutP806_trees_ok

theorem vcCutP807_outer : vcCutP807.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP807_roots vcCutP807_bounds_eq vcCutP807_trees_ok

theorem vcCutP808_outer : vcCutP808.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP808_roots vcCutP808_bounds_eq vcCutP808_trees_ok

theorem vcCutP809_outer : vcCutP809.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP809_roots vcCutP809_bounds_eq vcCutP809_trees_ok

theorem vcCutP810_outer : vcCutP810.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP810_roots vcCutP810_bounds_eq vcCutP810_trees_ok

theorem vcCutP811_outer : vcCutP811.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP811_roots vcCutP811_bounds_eq vcCutP811_trees_ok

theorem vcCutP812_outer : vcCutP812.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP812_roots vcCutP812_bounds_eq vcCutP812_trees_ok

theorem vcCutP813_outer : vcCutP813.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP813_roots vcCutP813_bounds_eq vcCutP813_trees_ok

theorem vcCutP814_outer : vcCutP814.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP814_roots vcCutP814_bounds_eq vcCutP814_trees_ok

theorem vcCutP815_outer : vcCutP815.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP815_roots vcCutP815_bounds_eq vcCutP815_trees_ok

theorem vcCutP816_outer : vcCutP816.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP816_roots vcCutP816_bounds_eq vcCutP816_trees_ok

theorem vcCutP817_outer : vcCutP817.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP817_roots vcCutP817_bounds_eq vcCutP817_trees_ok

theorem vcCutP818_outer : vcCutP818.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP818_roots vcCutP818_bounds_eq vcCutP818_trees_ok

theorem vcCutP819_outer : vcCutP819.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP819_roots vcCutP819_bounds_eq vcCutP819_trees_ok

theorem vcCutP820_outer : vcCutP820.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP820_roots vcCutP820_bounds_eq vcCutP820_trees_ok

theorem vcCutP821_outer : vcCutP821.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP821_roots vcCutP821_bounds_eq vcCutP821_trees_ok

theorem vcCutP822_outer : vcCutP822.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP822_roots vcCutP822_bounds_eq vcCutP822_trees_ok

theorem vcCutP823_outer : vcCutP823.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP823_roots vcCutP823_bounds_eq vcCutP823_trees_ok

theorem vcCutP824_outer : vcCutP824.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP824_roots vcCutP824_bounds_eq vcCutP824_trees_ok

theorem vcCutP825_outer : vcCutP825.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP825_roots vcCutP825_bounds_eq vcCutP825_trees_ok

theorem vcCutP826_outer : vcCutP826.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP826_roots vcCutP826_bounds_eq vcCutP826_trees_ok

theorem vcCutP827_outer : vcCutP827.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP827_roots vcCutP827_bounds_eq vcCutP827_trees_ok

theorem vcCutP828_outer : vcCutP828.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP828_roots vcCutP828_bounds_eq vcCutP828_trees_ok

theorem vcCutP829_outer : vcCutP829.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP829_roots vcCutP829_bounds_eq vcCutP829_trees_ok

theorem vcCutP830_outer : vcCutP830.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP830_roots vcCutP830_bounds_eq vcCutP830_trees_ok

theorem vcCutP831_outer : vcCutP831.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP831_roots vcCutP831_bounds_eq vcCutP831_trees_ok

theorem vcCutWitnesses800 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints800.toList :=
  ⟨vcCutP800_outer,
   vcCutP801_outer,
   vcCutP802_outer,
   vcCutP803_outer,
   vcCutP804_outer,
   vcCutP805_outer,
   vcCutP806_outer,
   vcCutP807_outer,
   vcCutP808_outer,
   vcCutP809_outer,
   vcCutP810_outer,
   vcCutP811_outer,
   vcCutP812_outer,
   vcCutP813_outer,
   vcCutP814_outer,
   vcCutP815_outer,
   vcCutP816_outer,
   vcCutP817_outer,
   vcCutP818_outer,
   vcCutP819_outer,
   vcCutP820_outer,
   vcCutP821_outer,
   vcCutP822_outer,
   vcCutP823_outer,
   vcCutP824_outer,
   vcCutP825_outer,
   vcCutP826_outer,
   vcCutP827_outer,
   vcCutP828_outer,
   vcCutP829_outer,
   vcCutP830_outer,
   vcCutP831_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
