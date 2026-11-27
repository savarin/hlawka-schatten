/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees640

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses640`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP640_outer : vcCutP640.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP640_roots vcCutP640_bounds_eq vcCutP640_trees_ok

theorem vcCutP641_outer : vcCutP641.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP641_roots vcCutP641_bounds_eq vcCutP641_trees_ok

theorem vcCutP642_outer : vcCutP642.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP642_roots vcCutP642_bounds_eq vcCutP642_trees_ok

theorem vcCutP643_outer : vcCutP643.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP643_roots vcCutP643_bounds_eq vcCutP643_trees_ok

theorem vcCutP644_outer : vcCutP644.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP644_roots vcCutP644_bounds_eq vcCutP644_trees_ok

theorem vcCutP645_outer : vcCutP645.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP645_roots vcCutP645_bounds_eq vcCutP645_trees_ok

theorem vcCutP646_outer : vcCutP646.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP646_roots vcCutP646_bounds_eq vcCutP646_trees_ok

theorem vcCutP647_outer : vcCutP647.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP647_roots vcCutP647_bounds_eq vcCutP647_trees_ok

theorem vcCutP648_outer : vcCutP648.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP648_roots vcCutP648_bounds_eq vcCutP648_trees_ok

theorem vcCutP649_outer : vcCutP649.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP649_roots vcCutP649_bounds_eq vcCutP649_trees_ok

theorem vcCutP650_outer : vcCutP650.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP650_roots vcCutP650_bounds_eq vcCutP650_trees_ok

theorem vcCutP651_outer : vcCutP651.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP651_roots vcCutP651_bounds_eq vcCutP651_trees_ok

theorem vcCutP652_outer : vcCutP652.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP652_roots vcCutP652_bounds_eq vcCutP652_trees_ok

theorem vcCutP653_outer : vcCutP653.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP653_roots vcCutP653_bounds_eq vcCutP653_trees_ok

theorem vcCutP654_outer : vcCutP654.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP654_roots vcCutP654_bounds_eq vcCutP654_trees_ok

theorem vcCutP655_outer : vcCutP655.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP655_roots vcCutP655_bounds_eq vcCutP655_trees_ok

theorem vcCutP656_outer : vcCutP656.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP656_roots vcCutP656_bounds_eq vcCutP656_trees_ok

theorem vcCutP657_outer : vcCutP657.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP657_roots vcCutP657_bounds_eq vcCutP657_trees_ok

theorem vcCutP658_outer : vcCutP658.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP658_roots vcCutP658_bounds_eq vcCutP658_trees_ok

theorem vcCutP659_outer : vcCutP659.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP659_roots vcCutP659_bounds_eq vcCutP659_trees_ok

theorem vcCutP660_outer : vcCutP660.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP660_roots vcCutP660_bounds_eq vcCutP660_trees_ok

theorem vcCutP661_outer : vcCutP661.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP661_roots vcCutP661_bounds_eq vcCutP661_trees_ok

theorem vcCutP662_outer : vcCutP662.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP662_roots vcCutP662_bounds_eq vcCutP662_trees_ok

theorem vcCutP663_outer : vcCutP663.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP663_roots vcCutP663_bounds_eq vcCutP663_trees_ok

theorem vcCutP664_outer : vcCutP664.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP664_roots vcCutP664_bounds_eq vcCutP664_trees_ok

theorem vcCutP665_outer : vcCutP665.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP665_roots vcCutP665_bounds_eq vcCutP665_trees_ok

theorem vcCutP666_outer : vcCutP666.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP666_roots vcCutP666_bounds_eq vcCutP666_trees_ok

theorem vcCutP667_outer : vcCutP667.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP667_roots vcCutP667_bounds_eq vcCutP667_trees_ok

theorem vcCutP668_outer : vcCutP668.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP668_roots vcCutP668_bounds_eq vcCutP668_trees_ok

theorem vcCutP669_outer : vcCutP669.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP669_roots vcCutP669_bounds_eq vcCutP669_trees_ok

theorem vcCutP670_outer : vcCutP670.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP670_roots vcCutP670_bounds_eq vcCutP670_trees_ok

theorem vcCutP671_outer : vcCutP671.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP671_roots vcCutP671_bounds_eq vcCutP671_trees_ok

theorem vcCutWitnesses640 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints640.toList :=
  ⟨vcCutP640_outer,
   vcCutP641_outer,
   vcCutP642_outer,
   vcCutP643_outer,
   vcCutP644_outer,
   vcCutP645_outer,
   vcCutP646_outer,
   vcCutP647_outer,
   vcCutP648_outer,
   vcCutP649_outer,
   vcCutP650_outer,
   vcCutP651_outer,
   vcCutP652_outer,
   vcCutP653_outer,
   vcCutP654_outer,
   vcCutP655_outer,
   vcCutP656_outer,
   vcCutP657_outer,
   vcCutP658_outer,
   vcCutP659_outer,
   vcCutP660_outer,
   vcCutP661_outer,
   vcCutP662_outer,
   vcCutP663_outer,
   vcCutP664_outer,
   vcCutP665_outer,
   vcCutP666_outer,
   vcCutP667_outer,
   vcCutP668_outer,
   vcCutP669_outer,
   vcCutP670_outer,
   vcCutP671_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
