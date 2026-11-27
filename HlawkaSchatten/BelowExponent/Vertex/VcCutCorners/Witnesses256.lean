/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees256

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses256`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP256_outer : vcCutP256.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP256_roots vcCutP256_bounds_eq vcCutP256_trees_ok

theorem vcCutP257_outer : vcCutP257.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP257_roots vcCutP257_bounds_eq vcCutP257_trees_ok

theorem vcCutP258_outer : vcCutP258.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP258_roots vcCutP258_bounds_eq vcCutP258_trees_ok

theorem vcCutP259_outer : vcCutP259.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP259_roots vcCutP259_bounds_eq vcCutP259_trees_ok

theorem vcCutP260_outer : vcCutP260.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP260_roots vcCutP260_bounds_eq vcCutP260_trees_ok

theorem vcCutP261_outer : vcCutP261.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP261_roots vcCutP261_bounds_eq vcCutP261_trees_ok

theorem vcCutP262_outer : vcCutP262.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP262_roots vcCutP262_bounds_eq vcCutP262_trees_ok

theorem vcCutP263_outer : vcCutP263.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP263_roots vcCutP263_bounds_eq vcCutP263_trees_ok

theorem vcCutP264_outer : vcCutP264.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP264_roots vcCutP264_bounds_eq vcCutP264_trees_ok

theorem vcCutP265_outer : vcCutP265.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP265_roots vcCutP265_bounds_eq vcCutP265_trees_ok

theorem vcCutP266_outer : vcCutP266.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP266_roots vcCutP266_bounds_eq vcCutP266_trees_ok

theorem vcCutP267_outer : vcCutP267.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP267_roots vcCutP267_bounds_eq vcCutP267_trees_ok

theorem vcCutP268_outer : vcCutP268.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP268_roots vcCutP268_bounds_eq vcCutP268_trees_ok

theorem vcCutP269_outer : vcCutP269.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP269_roots vcCutP269_bounds_eq vcCutP269_trees_ok

theorem vcCutP270_outer : vcCutP270.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP270_roots vcCutP270_bounds_eq vcCutP270_trees_ok

theorem vcCutP271_outer : vcCutP271.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP271_roots vcCutP271_bounds_eq vcCutP271_trees_ok

theorem vcCutP272_outer : vcCutP272.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP272_roots vcCutP272_bounds_eq vcCutP272_trees_ok

theorem vcCutP273_outer : vcCutP273.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP273_roots vcCutP273_bounds_eq vcCutP273_trees_ok

theorem vcCutP274_outer : vcCutP274.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP274_roots vcCutP274_bounds_eq vcCutP274_trees_ok

theorem vcCutP275_outer : vcCutP275.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP275_roots vcCutP275_bounds_eq vcCutP275_trees_ok

theorem vcCutP276_outer : vcCutP276.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP276_roots vcCutP276_bounds_eq vcCutP276_trees_ok

theorem vcCutP277_outer : vcCutP277.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP277_roots vcCutP277_bounds_eq vcCutP277_trees_ok

theorem vcCutP278_outer : vcCutP278.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP278_roots vcCutP278_bounds_eq vcCutP278_trees_ok

theorem vcCutP279_outer : vcCutP279.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP279_roots vcCutP279_bounds_eq vcCutP279_trees_ok

theorem vcCutP280_outer : vcCutP280.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP280_roots vcCutP280_bounds_eq vcCutP280_trees_ok

theorem vcCutP281_outer : vcCutP281.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP281_roots vcCutP281_bounds_eq vcCutP281_trees_ok

theorem vcCutP282_outer : vcCutP282.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP282_roots vcCutP282_bounds_eq vcCutP282_trees_ok

theorem vcCutP283_outer : vcCutP283.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP283_roots vcCutP283_bounds_eq vcCutP283_trees_ok

theorem vcCutP284_outer : vcCutP284.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP284_roots vcCutP284_bounds_eq vcCutP284_trees_ok

theorem vcCutP285_outer : vcCutP285.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP285_roots vcCutP285_bounds_eq vcCutP285_trees_ok

theorem vcCutP286_outer : vcCutP286.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP286_roots vcCutP286_bounds_eq vcCutP286_trees_ok

theorem vcCutP287_outer : vcCutP287.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP287_roots vcCutP287_bounds_eq vcCutP287_trees_ok

theorem vcCutWitnesses256 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints256.toList :=
  ⟨vcCutP256_outer,
   vcCutP257_outer,
   vcCutP258_outer,
   vcCutP259_outer,
   vcCutP260_outer,
   vcCutP261_outer,
   vcCutP262_outer,
   vcCutP263_outer,
   vcCutP264_outer,
   vcCutP265_outer,
   vcCutP266_outer,
   vcCutP267_outer,
   vcCutP268_outer,
   vcCutP269_outer,
   vcCutP270_outer,
   vcCutP271_outer,
   vcCutP272_outer,
   vcCutP273_outer,
   vcCutP274_outer,
   vcCutP275_outer,
   vcCutP276_outer,
   vcCutP277_outer,
   vcCutP278_outer,
   vcCutP279_outer,
   vcCutP280_outer,
   vcCutP281_outer,
   vcCutP282_outer,
   vcCutP283_outer,
   vcCutP284_outer,
   vcCutP285_outer,
   vcCutP286_outer,
   vcCutP287_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
