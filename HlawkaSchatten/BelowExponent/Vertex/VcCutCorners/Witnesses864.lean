/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees864

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses864`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP864_outer : vcCutP864.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP864_roots vcCutP864_bounds_eq vcCutP864_trees_ok

theorem vcCutP865_outer : vcCutP865.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP865_roots vcCutP865_bounds_eq vcCutP865_trees_ok

theorem vcCutP866_outer : vcCutP866.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP866_roots vcCutP866_bounds_eq vcCutP866_trees_ok

theorem vcCutP867_outer : vcCutP867.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP867_roots vcCutP867_bounds_eq vcCutP867_trees_ok

theorem vcCutP868_outer : vcCutP868.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP868_roots vcCutP868_bounds_eq vcCutP868_trees_ok

theorem vcCutP869_outer : vcCutP869.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP869_roots vcCutP869_bounds_eq vcCutP869_trees_ok

theorem vcCutP870_outer : vcCutP870.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP870_roots vcCutP870_bounds_eq vcCutP870_trees_ok

theorem vcCutP871_outer : vcCutP871.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP871_roots vcCutP871_bounds_eq vcCutP871_trees_ok

theorem vcCutP872_outer : vcCutP872.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP872_roots vcCutP872_bounds_eq vcCutP872_trees_ok

theorem vcCutP873_outer : vcCutP873.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP873_roots vcCutP873_bounds_eq vcCutP873_trees_ok

theorem vcCutP874_outer : vcCutP874.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP874_roots vcCutP874_bounds_eq vcCutP874_trees_ok

theorem vcCutP875_outer : vcCutP875.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP875_roots vcCutP875_bounds_eq vcCutP875_trees_ok

theorem vcCutP876_outer : vcCutP876.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP876_roots vcCutP876_bounds_eq vcCutP876_trees_ok

theorem vcCutP877_outer : vcCutP877.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP877_roots vcCutP877_bounds_eq vcCutP877_trees_ok

theorem vcCutP878_outer : vcCutP878.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP878_roots vcCutP878_bounds_eq vcCutP878_trees_ok

theorem vcCutP879_outer : vcCutP879.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP879_roots vcCutP879_bounds_eq vcCutP879_trees_ok

theorem vcCutP880_outer : vcCutP880.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP880_roots vcCutP880_bounds_eq vcCutP880_trees_ok

theorem vcCutP881_outer : vcCutP881.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP881_roots vcCutP881_bounds_eq vcCutP881_trees_ok

theorem vcCutWitnesses864 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints864.toList :=
  ⟨vcCutP864_outer,
   vcCutP865_outer,
   vcCutP866_outer,
   vcCutP867_outer,
   vcCutP868_outer,
   vcCutP869_outer,
   vcCutP870_outer,
   vcCutP871_outer,
   vcCutP872_outer,
   vcCutP873_outer,
   vcCutP874_outer,
   vcCutP875_outer,
   vcCutP876_outer,
   vcCutP877_outer,
   vcCutP878_outer,
   vcCutP879_outer,
   vcCutP880_outer,
   vcCutP881_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
