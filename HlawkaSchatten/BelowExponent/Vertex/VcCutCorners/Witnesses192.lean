/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees192

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses192`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP192_outer : vcCutP192.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP192_roots vcCutP192_bounds_eq vcCutP192_trees_ok

theorem vcCutP193_outer : vcCutP193.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP193_roots vcCutP193_bounds_eq vcCutP193_trees_ok

theorem vcCutP194_outer : vcCutP194.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP194_roots vcCutP194_bounds_eq vcCutP194_trees_ok

theorem vcCutP195_outer : vcCutP195.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP195_roots vcCutP195_bounds_eq vcCutP195_trees_ok

theorem vcCutP196_outer : vcCutP196.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP196_roots vcCutP196_bounds_eq vcCutP196_trees_ok

theorem vcCutP197_outer : vcCutP197.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP197_roots vcCutP197_bounds_eq vcCutP197_trees_ok

theorem vcCutP198_outer : vcCutP198.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP198_roots vcCutP198_bounds_eq vcCutP198_trees_ok

theorem vcCutP199_outer : vcCutP199.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP199_roots vcCutP199_bounds_eq vcCutP199_trees_ok

theorem vcCutP200_outer : vcCutP200.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP200_roots vcCutP200_bounds_eq vcCutP200_trees_ok

theorem vcCutP201_outer : vcCutP201.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP201_roots vcCutP201_bounds_eq vcCutP201_trees_ok

theorem vcCutP202_outer : vcCutP202.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP202_roots vcCutP202_bounds_eq vcCutP202_trees_ok

theorem vcCutP203_outer : vcCutP203.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP203_roots vcCutP203_bounds_eq vcCutP203_trees_ok

theorem vcCutP204_outer : vcCutP204.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP204_roots vcCutP204_bounds_eq vcCutP204_trees_ok

theorem vcCutP205_outer : vcCutP205.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP205_roots vcCutP205_bounds_eq vcCutP205_trees_ok

theorem vcCutP206_outer : vcCutP206.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP206_roots vcCutP206_bounds_eq vcCutP206_trees_ok

theorem vcCutP207_outer : vcCutP207.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP207_roots vcCutP207_bounds_eq vcCutP207_trees_ok

theorem vcCutP208_outer : vcCutP208.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP208_roots vcCutP208_bounds_eq vcCutP208_trees_ok

theorem vcCutP209_outer : vcCutP209.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP209_roots vcCutP209_bounds_eq vcCutP209_trees_ok

theorem vcCutP210_outer : vcCutP210.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP210_roots vcCutP210_bounds_eq vcCutP210_trees_ok

theorem vcCutP211_outer : vcCutP211.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP211_roots vcCutP211_bounds_eq vcCutP211_trees_ok

theorem vcCutP212_outer : vcCutP212.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP212_roots vcCutP212_bounds_eq vcCutP212_trees_ok

theorem vcCutP213_outer : vcCutP213.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP213_roots vcCutP213_bounds_eq vcCutP213_trees_ok

theorem vcCutP214_outer : vcCutP214.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP214_roots vcCutP214_bounds_eq vcCutP214_trees_ok

theorem vcCutP215_outer : vcCutP215.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP215_roots vcCutP215_bounds_eq vcCutP215_trees_ok

theorem vcCutP216_outer : vcCutP216.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP216_roots vcCutP216_bounds_eq vcCutP216_trees_ok

theorem vcCutP217_outer : vcCutP217.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP217_roots vcCutP217_bounds_eq vcCutP217_trees_ok

theorem vcCutP218_outer : vcCutP218.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP218_roots vcCutP218_bounds_eq vcCutP218_trees_ok

theorem vcCutP219_outer : vcCutP219.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP219_roots vcCutP219_bounds_eq vcCutP219_trees_ok

theorem vcCutP220_outer : vcCutP220.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP220_roots vcCutP220_bounds_eq vcCutP220_trees_ok

theorem vcCutP221_outer : vcCutP221.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP221_roots vcCutP221_bounds_eq vcCutP221_trees_ok

theorem vcCutP222_outer : vcCutP222.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP222_roots vcCutP222_bounds_eq vcCutP222_trees_ok

theorem vcCutP223_outer : vcCutP223.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP223_roots vcCutP223_bounds_eq vcCutP223_trees_ok

theorem vcCutWitnesses192 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints192.toList :=
  ⟨vcCutP192_outer,
   vcCutP193_outer,
   vcCutP194_outer,
   vcCutP195_outer,
   vcCutP196_outer,
   vcCutP197_outer,
   vcCutP198_outer,
   vcCutP199_outer,
   vcCutP200_outer,
   vcCutP201_outer,
   vcCutP202_outer,
   vcCutP203_outer,
   vcCutP204_outer,
   vcCutP205_outer,
   vcCutP206_outer,
   vcCutP207_outer,
   vcCutP208_outer,
   vcCutP209_outer,
   vcCutP210_outer,
   vcCutP211_outer,
   vcCutP212_outer,
   vcCutP213_outer,
   vcCutP214_outer,
   vcCutP215_outer,
   vcCutP216_outer,
   vcCutP217_outer,
   vcCutP218_outer,
   vcCutP219_outer,
   vcCutP220_outer,
   vcCutP221_outer,
   vcCutP222_outer,
   vcCutP223_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
