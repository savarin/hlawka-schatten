/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees160

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses160`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP160_outer : vcCutP160.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP160_roots vcCutP160_bounds_eq vcCutP160_trees_ok

theorem vcCutP161_outer : vcCutP161.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP161_roots vcCutP161_bounds_eq vcCutP161_trees_ok

theorem vcCutP162_outer : vcCutP162.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP162_roots vcCutP162_bounds_eq vcCutP162_trees_ok

theorem vcCutP163_outer : vcCutP163.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP163_roots vcCutP163_bounds_eq vcCutP163_trees_ok

theorem vcCutP164_outer : vcCutP164.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP164_roots vcCutP164_bounds_eq vcCutP164_trees_ok

theorem vcCutP165_outer : vcCutP165.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP165_roots vcCutP165_bounds_eq vcCutP165_trees_ok

theorem vcCutP166_outer : vcCutP166.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP166_roots vcCutP166_bounds_eq vcCutP166_trees_ok

theorem vcCutP167_outer : vcCutP167.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP167_roots vcCutP167_bounds_eq vcCutP167_trees_ok

theorem vcCutP168_outer : vcCutP168.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP168_roots vcCutP168_bounds_eq vcCutP168_trees_ok

theorem vcCutP169_outer : vcCutP169.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP169_roots vcCutP169_bounds_eq vcCutP169_trees_ok

theorem vcCutP170_outer : vcCutP170.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP170_roots vcCutP170_bounds_eq vcCutP170_trees_ok

theorem vcCutP171_outer : vcCutP171.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP171_roots vcCutP171_bounds_eq vcCutP171_trees_ok

theorem vcCutP172_outer : vcCutP172.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP172_roots vcCutP172_bounds_eq vcCutP172_trees_ok

theorem vcCutP173_outer : vcCutP173.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP173_roots vcCutP173_bounds_eq vcCutP173_trees_ok

theorem vcCutP174_outer : vcCutP174.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP174_roots vcCutP174_bounds_eq vcCutP174_trees_ok

theorem vcCutP175_outer : vcCutP175.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP175_roots vcCutP175_bounds_eq vcCutP175_trees_ok

theorem vcCutP176_outer : vcCutP176.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP176_roots vcCutP176_bounds_eq vcCutP176_trees_ok

theorem vcCutP177_outer : vcCutP177.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP177_roots vcCutP177_bounds_eq vcCutP177_trees_ok

theorem vcCutP178_outer : vcCutP178.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP178_roots vcCutP178_bounds_eq vcCutP178_trees_ok

theorem vcCutP179_outer : vcCutP179.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP179_roots vcCutP179_bounds_eq vcCutP179_trees_ok

theorem vcCutP180_outer : vcCutP180.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP180_roots vcCutP180_bounds_eq vcCutP180_trees_ok

theorem vcCutP181_outer : vcCutP181.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP181_roots vcCutP181_bounds_eq vcCutP181_trees_ok

theorem vcCutP182_outer : vcCutP182.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP182_roots vcCutP182_bounds_eq vcCutP182_trees_ok

theorem vcCutP183_outer : vcCutP183.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP183_roots vcCutP183_bounds_eq vcCutP183_trees_ok

theorem vcCutP184_outer : vcCutP184.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP184_roots vcCutP184_bounds_eq vcCutP184_trees_ok

theorem vcCutP185_outer : vcCutP185.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP185_roots vcCutP185_bounds_eq vcCutP185_trees_ok

theorem vcCutP186_outer : vcCutP186.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP186_roots vcCutP186_bounds_eq vcCutP186_trees_ok

theorem vcCutP187_outer : vcCutP187.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP187_roots vcCutP187_bounds_eq vcCutP187_trees_ok

theorem vcCutP188_outer : vcCutP188.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP188_roots vcCutP188_bounds_eq vcCutP188_trees_ok

theorem vcCutP189_outer : vcCutP189.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP189_roots vcCutP189_bounds_eq vcCutP189_trees_ok

theorem vcCutP190_outer : vcCutP190.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP190_roots vcCutP190_bounds_eq vcCutP190_trees_ok

theorem vcCutP191_outer : vcCutP191.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP191_roots vcCutP191_bounds_eq vcCutP191_trees_ok

theorem vcCutWitnesses160 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints160.toList :=
  ⟨vcCutP160_outer,
   vcCutP161_outer,
   vcCutP162_outer,
   vcCutP163_outer,
   vcCutP164_outer,
   vcCutP165_outer,
   vcCutP166_outer,
   vcCutP167_outer,
   vcCutP168_outer,
   vcCutP169_outer,
   vcCutP170_outer,
   vcCutP171_outer,
   vcCutP172_outer,
   vcCutP173_outer,
   vcCutP174_outer,
   vcCutP175_outer,
   vcCutP176_outer,
   vcCutP177_outer,
   vcCutP178_outer,
   vcCutP179_outer,
   vcCutP180_outer,
   vcCutP181_outer,
   vcCutP182_outer,
   vcCutP183_outer,
   vcCutP184_outer,
   vcCutP185_outer,
   vcCutP186_outer,
   vcCutP187_outer,
   vcCutP188_outer,
   vcCutP189_outer,
   vcCutP190_outer,
   vcCutP191_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
