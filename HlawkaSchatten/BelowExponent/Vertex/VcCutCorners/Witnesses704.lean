/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees704

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses704`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP704_outer : vcCutP704.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP704_roots vcCutP704_bounds_eq vcCutP704_trees_ok

theorem vcCutP705_outer : vcCutP705.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP705_roots vcCutP705_bounds_eq vcCutP705_trees_ok

theorem vcCutP706_outer : vcCutP706.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP706_roots vcCutP706_bounds_eq vcCutP706_trees_ok

theorem vcCutP707_outer : vcCutP707.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP707_roots vcCutP707_bounds_eq vcCutP707_trees_ok

theorem vcCutP708_outer : vcCutP708.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP708_roots vcCutP708_bounds_eq vcCutP708_trees_ok

theorem vcCutP709_outer : vcCutP709.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP709_roots vcCutP709_bounds_eq vcCutP709_trees_ok

theorem vcCutP710_outer : vcCutP710.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP710_roots vcCutP710_bounds_eq vcCutP710_trees_ok

theorem vcCutP711_outer : vcCutP711.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP711_roots vcCutP711_bounds_eq vcCutP711_trees_ok

theorem vcCutP712_outer : vcCutP712.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP712_roots vcCutP712_bounds_eq vcCutP712_trees_ok

theorem vcCutP713_outer : vcCutP713.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP713_roots vcCutP713_bounds_eq vcCutP713_trees_ok

theorem vcCutP714_outer : vcCutP714.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP714_roots vcCutP714_bounds_eq vcCutP714_trees_ok

theorem vcCutP715_outer : vcCutP715.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP715_roots vcCutP715_bounds_eq vcCutP715_trees_ok

theorem vcCutP716_outer : vcCutP716.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP716_roots vcCutP716_bounds_eq vcCutP716_trees_ok

theorem vcCutP717_outer : vcCutP717.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP717_roots vcCutP717_bounds_eq vcCutP717_trees_ok

theorem vcCutP718_outer : vcCutP718.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP718_roots vcCutP718_bounds_eq vcCutP718_trees_ok

theorem vcCutP719_outer : vcCutP719.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP719_roots vcCutP719_bounds_eq vcCutP719_trees_ok

theorem vcCutP720_outer : vcCutP720.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP720_roots vcCutP720_bounds_eq vcCutP720_trees_ok

theorem vcCutP721_outer : vcCutP721.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP721_roots vcCutP721_bounds_eq vcCutP721_trees_ok

theorem vcCutP722_outer : vcCutP722.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP722_roots vcCutP722_bounds_eq vcCutP722_trees_ok

theorem vcCutP723_outer : vcCutP723.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP723_roots vcCutP723_bounds_eq vcCutP723_trees_ok

theorem vcCutP724_outer : vcCutP724.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP724_roots vcCutP724_bounds_eq vcCutP724_trees_ok

theorem vcCutP725_outer : vcCutP725.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP725_roots vcCutP725_bounds_eq vcCutP725_trees_ok

theorem vcCutP726_outer : vcCutP726.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP726_roots vcCutP726_bounds_eq vcCutP726_trees_ok

theorem vcCutP727_outer : vcCutP727.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP727_roots vcCutP727_bounds_eq vcCutP727_trees_ok

theorem vcCutP728_outer : vcCutP728.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP728_roots vcCutP728_bounds_eq vcCutP728_trees_ok

theorem vcCutP729_outer : vcCutP729.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP729_roots vcCutP729_bounds_eq vcCutP729_trees_ok

theorem vcCutP730_outer : vcCutP730.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP730_roots vcCutP730_bounds_eq vcCutP730_trees_ok

theorem vcCutP731_outer : vcCutP731.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP731_roots vcCutP731_bounds_eq vcCutP731_trees_ok

theorem vcCutP732_outer : vcCutP732.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP732_roots vcCutP732_bounds_eq vcCutP732_trees_ok

theorem vcCutP733_outer : vcCutP733.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP733_roots vcCutP733_bounds_eq vcCutP733_trees_ok

theorem vcCutP734_outer : vcCutP734.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP734_roots vcCutP734_bounds_eq vcCutP734_trees_ok

theorem vcCutP735_outer : vcCutP735.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP735_roots vcCutP735_bounds_eq vcCutP735_trees_ok

theorem vcCutWitnesses704 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints704.toList :=
  ⟨vcCutP704_outer,
   vcCutP705_outer,
   vcCutP706_outer,
   vcCutP707_outer,
   vcCutP708_outer,
   vcCutP709_outer,
   vcCutP710_outer,
   vcCutP711_outer,
   vcCutP712_outer,
   vcCutP713_outer,
   vcCutP714_outer,
   vcCutP715_outer,
   vcCutP716_outer,
   vcCutP717_outer,
   vcCutP718_outer,
   vcCutP719_outer,
   vcCutP720_outer,
   vcCutP721_outer,
   vcCutP722_outer,
   vcCutP723_outer,
   vcCutP724_outer,
   vcCutP725_outer,
   vcCutP726_outer,
   vcCutP727_outer,
   vcCutP728_outer,
   vcCutP729_outer,
   vcCutP730_outer,
   vcCutP731_outer,
   vcCutP732_outer,
   vcCutP733_outer,
   vcCutP734_outer,
   vcCutP735_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
