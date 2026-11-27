/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees224

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses224`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP224_outer : vcCutP224.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP224_roots vcCutP224_bounds_eq vcCutP224_trees_ok

theorem vcCutP225_outer : vcCutP225.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP225_roots vcCutP225_bounds_eq vcCutP225_trees_ok

theorem vcCutP226_outer : vcCutP226.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP226_roots vcCutP226_bounds_eq vcCutP226_trees_ok

theorem vcCutP227_outer : vcCutP227.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP227_roots vcCutP227_bounds_eq vcCutP227_trees_ok

theorem vcCutP228_outer : vcCutP228.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP228_roots vcCutP228_bounds_eq vcCutP228_trees_ok

theorem vcCutP229_outer : vcCutP229.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP229_roots vcCutP229_bounds_eq vcCutP229_trees_ok

theorem vcCutP230_outer : vcCutP230.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP230_roots vcCutP230_bounds_eq vcCutP230_trees_ok

theorem vcCutP231_outer : vcCutP231.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP231_roots vcCutP231_bounds_eq vcCutP231_trees_ok

theorem vcCutP232_outer : vcCutP232.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP232_roots vcCutP232_bounds_eq vcCutP232_trees_ok

theorem vcCutP233_outer : vcCutP233.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP233_roots vcCutP233_bounds_eq vcCutP233_trees_ok

theorem vcCutP234_outer : vcCutP234.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP234_roots vcCutP234_bounds_eq vcCutP234_trees_ok

theorem vcCutP235_outer : vcCutP235.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP235_roots vcCutP235_bounds_eq vcCutP235_trees_ok

theorem vcCutP236_outer : vcCutP236.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP236_roots vcCutP236_bounds_eq vcCutP236_trees_ok

theorem vcCutP237_outer : vcCutP237.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP237_roots vcCutP237_bounds_eq vcCutP237_trees_ok

theorem vcCutP238_outer : vcCutP238.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP238_roots vcCutP238_bounds_eq vcCutP238_trees_ok

theorem vcCutP239_outer : vcCutP239.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP239_roots vcCutP239_bounds_eq vcCutP239_trees_ok

theorem vcCutP240_outer : vcCutP240.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP240_roots vcCutP240_bounds_eq vcCutP240_trees_ok

theorem vcCutP241_outer : vcCutP241.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP241_roots vcCutP241_bounds_eq vcCutP241_trees_ok

theorem vcCutP242_outer : vcCutP242.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP242_roots vcCutP242_bounds_eq vcCutP242_trees_ok

theorem vcCutP243_outer : vcCutP243.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP243_roots vcCutP243_bounds_eq vcCutP243_trees_ok

theorem vcCutP244_outer : vcCutP244.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP244_roots vcCutP244_bounds_eq vcCutP244_trees_ok

theorem vcCutP245_outer : vcCutP245.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP245_roots vcCutP245_bounds_eq vcCutP245_trees_ok

theorem vcCutP246_outer : vcCutP246.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP246_roots vcCutP246_bounds_eq vcCutP246_trees_ok

theorem vcCutP247_outer : vcCutP247.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP247_roots vcCutP247_bounds_eq vcCutP247_trees_ok

theorem vcCutP248_outer : vcCutP248.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP248_roots vcCutP248_bounds_eq vcCutP248_trees_ok

theorem vcCutP249_outer : vcCutP249.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP249_roots vcCutP249_bounds_eq vcCutP249_trees_ok

theorem vcCutP250_outer : vcCutP250.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP250_roots vcCutP250_bounds_eq vcCutP250_trees_ok

theorem vcCutP251_outer : vcCutP251.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP251_roots vcCutP251_bounds_eq vcCutP251_trees_ok

theorem vcCutP252_outer : vcCutP252.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP252_roots vcCutP252_bounds_eq vcCutP252_trees_ok

theorem vcCutP253_outer : vcCutP253.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP253_roots vcCutP253_bounds_eq vcCutP253_trees_ok

theorem vcCutP254_outer : vcCutP254.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP254_roots vcCutP254_bounds_eq vcCutP254_trees_ok

theorem vcCutP255_outer : vcCutP255.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP255_roots vcCutP255_bounds_eq vcCutP255_trees_ok

theorem vcCutWitnesses224 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints224.toList :=
  ⟨vcCutP224_outer,
   vcCutP225_outer,
   vcCutP226_outer,
   vcCutP227_outer,
   vcCutP228_outer,
   vcCutP229_outer,
   vcCutP230_outer,
   vcCutP231_outer,
   vcCutP232_outer,
   vcCutP233_outer,
   vcCutP234_outer,
   vcCutP235_outer,
   vcCutP236_outer,
   vcCutP237_outer,
   vcCutP238_outer,
   vcCutP239_outer,
   vcCutP240_outer,
   vcCutP241_outer,
   vcCutP242_outer,
   vcCutP243_outer,
   vcCutP244_outer,
   vcCutP245_outer,
   vcCutP246_outer,
   vcCutP247_outer,
   vcCutP248_outer,
   vcCutP249_outer,
   vcCutP250_outer,
   vcCutP251_outer,
   vcCutP252_outer,
   vcCutP253_outer,
   vcCutP254_outer,
   vcCutP255_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
