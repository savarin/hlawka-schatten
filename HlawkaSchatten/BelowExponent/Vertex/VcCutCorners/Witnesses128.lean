/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees128

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses128`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP128_outer : vcCutP128.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP128_roots vcCutP128_bounds_eq vcCutP128_trees_ok

theorem vcCutP129_outer : vcCutP129.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP129_roots vcCutP129_bounds_eq vcCutP129_trees_ok

theorem vcCutP130_outer : vcCutP130.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP130_roots vcCutP130_bounds_eq vcCutP130_trees_ok

theorem vcCutP131_outer : vcCutP131.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP131_roots vcCutP131_bounds_eq vcCutP131_trees_ok

theorem vcCutP132_outer : vcCutP132.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP132_roots vcCutP132_bounds_eq vcCutP132_trees_ok

theorem vcCutP133_outer : vcCutP133.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP133_roots vcCutP133_bounds_eq vcCutP133_trees_ok

theorem vcCutP134_outer : vcCutP134.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP134_roots vcCutP134_bounds_eq vcCutP134_trees_ok

theorem vcCutP135_outer : vcCutP135.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP135_roots vcCutP135_bounds_eq vcCutP135_trees_ok

theorem vcCutP136_outer : vcCutP136.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP136_roots vcCutP136_bounds_eq vcCutP136_trees_ok

theorem vcCutP137_outer : vcCutP137.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP137_roots vcCutP137_bounds_eq vcCutP137_trees_ok

theorem vcCutP138_outer : vcCutP138.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP138_roots vcCutP138_bounds_eq vcCutP138_trees_ok

theorem vcCutP139_outer : vcCutP139.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP139_roots vcCutP139_bounds_eq vcCutP139_trees_ok

theorem vcCutP140_outer : vcCutP140.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP140_roots vcCutP140_bounds_eq vcCutP140_trees_ok

theorem vcCutP141_outer : vcCutP141.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP141_roots vcCutP141_bounds_eq vcCutP141_trees_ok

theorem vcCutP142_outer : vcCutP142.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP142_roots vcCutP142_bounds_eq vcCutP142_trees_ok

theorem vcCutP143_outer : vcCutP143.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP143_roots vcCutP143_bounds_eq vcCutP143_trees_ok

theorem vcCutP144_outer : vcCutP144.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP144_roots vcCutP144_bounds_eq vcCutP144_trees_ok

theorem vcCutP145_outer : vcCutP145.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP145_roots vcCutP145_bounds_eq vcCutP145_trees_ok

theorem vcCutP146_outer : vcCutP146.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP146_roots vcCutP146_bounds_eq vcCutP146_trees_ok

theorem vcCutP147_outer : vcCutP147.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP147_roots vcCutP147_bounds_eq vcCutP147_trees_ok

theorem vcCutP148_outer : vcCutP148.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP148_roots vcCutP148_bounds_eq vcCutP148_trees_ok

theorem vcCutP149_outer : vcCutP149.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP149_roots vcCutP149_bounds_eq vcCutP149_trees_ok

theorem vcCutP150_outer : vcCutP150.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP150_roots vcCutP150_bounds_eq vcCutP150_trees_ok

theorem vcCutP151_outer : vcCutP151.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP151_roots vcCutP151_bounds_eq vcCutP151_trees_ok

theorem vcCutP152_outer : vcCutP152.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP152_roots vcCutP152_bounds_eq vcCutP152_trees_ok

theorem vcCutP153_outer : vcCutP153.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP153_roots vcCutP153_bounds_eq vcCutP153_trees_ok

theorem vcCutP154_outer : vcCutP154.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP154_roots vcCutP154_bounds_eq vcCutP154_trees_ok

theorem vcCutP155_outer : vcCutP155.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP155_roots vcCutP155_bounds_eq vcCutP155_trees_ok

theorem vcCutP156_outer : vcCutP156.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP156_roots vcCutP156_bounds_eq vcCutP156_trees_ok

theorem vcCutP157_outer : vcCutP157.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP157_roots vcCutP157_bounds_eq vcCutP157_trees_ok

theorem vcCutP158_outer : vcCutP158.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP158_roots vcCutP158_bounds_eq vcCutP158_trees_ok

theorem vcCutP159_outer : vcCutP159.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP159_roots vcCutP159_bounds_eq vcCutP159_trees_ok

theorem vcCutWitnesses128 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints128.toList :=
  ⟨vcCutP128_outer,
   vcCutP129_outer,
   vcCutP130_outer,
   vcCutP131_outer,
   vcCutP132_outer,
   vcCutP133_outer,
   vcCutP134_outer,
   vcCutP135_outer,
   vcCutP136_outer,
   vcCutP137_outer,
   vcCutP138_outer,
   vcCutP139_outer,
   vcCutP140_outer,
   vcCutP141_outer,
   vcCutP142_outer,
   vcCutP143_outer,
   vcCutP144_outer,
   vcCutP145_outer,
   vcCutP146_outer,
   vcCutP147_outer,
   vcCutP148_outer,
   vcCutP149_outer,
   vcCutP150_outer,
   vcCutP151_outer,
   vcCutP152_outer,
   vcCutP153_outer,
   vcCutP154_outer,
   vcCutP155_outer,
   vcCutP156_outer,
   vcCutP157_outer,
   vcCutP158_outer,
   vcCutP159_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
