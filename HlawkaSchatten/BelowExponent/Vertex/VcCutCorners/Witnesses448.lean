/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees448

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses448`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP448_outer : vcCutP448.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP448_roots vcCutP448_bounds_eq vcCutP448_trees_ok

theorem vcCutP449_outer : vcCutP449.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP449_roots vcCutP449_bounds_eq vcCutP449_trees_ok

theorem vcCutP450_outer : vcCutP450.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP450_roots vcCutP450_bounds_eq vcCutP450_trees_ok

theorem vcCutP451_outer : vcCutP451.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP451_roots vcCutP451_bounds_eq vcCutP451_trees_ok

theorem vcCutP452_outer : vcCutP452.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP452_roots vcCutP452_bounds_eq vcCutP452_trees_ok

theorem vcCutP453_outer : vcCutP453.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP453_roots vcCutP453_bounds_eq vcCutP453_trees_ok

theorem vcCutP454_outer : vcCutP454.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP454_roots vcCutP454_bounds_eq vcCutP454_trees_ok

theorem vcCutP455_outer : vcCutP455.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP455_roots vcCutP455_bounds_eq vcCutP455_trees_ok

theorem vcCutP456_outer : vcCutP456.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP456_roots vcCutP456_bounds_eq vcCutP456_trees_ok

theorem vcCutP457_outer : vcCutP457.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP457_roots vcCutP457_bounds_eq vcCutP457_trees_ok

theorem vcCutP458_outer : vcCutP458.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP458_roots vcCutP458_bounds_eq vcCutP458_trees_ok

theorem vcCutP459_outer : vcCutP459.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP459_roots vcCutP459_bounds_eq vcCutP459_trees_ok

theorem vcCutP460_outer : vcCutP460.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP460_roots vcCutP460_bounds_eq vcCutP460_trees_ok

theorem vcCutP461_outer : vcCutP461.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP461_roots vcCutP461_bounds_eq vcCutP461_trees_ok

theorem vcCutP462_outer : vcCutP462.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP462_roots vcCutP462_bounds_eq vcCutP462_trees_ok

theorem vcCutP463_outer : vcCutP463.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP463_roots vcCutP463_bounds_eq vcCutP463_trees_ok

theorem vcCutP464_outer : vcCutP464.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP464_roots vcCutP464_bounds_eq vcCutP464_trees_ok

theorem vcCutP465_outer : vcCutP465.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP465_roots vcCutP465_bounds_eq vcCutP465_trees_ok

theorem vcCutP466_outer : vcCutP466.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP466_roots vcCutP466_bounds_eq vcCutP466_trees_ok

theorem vcCutP467_outer : vcCutP467.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP467_roots vcCutP467_bounds_eq vcCutP467_trees_ok

theorem vcCutP468_outer : vcCutP468.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP468_roots vcCutP468_bounds_eq vcCutP468_trees_ok

theorem vcCutP469_outer : vcCutP469.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP469_roots vcCutP469_bounds_eq vcCutP469_trees_ok

theorem vcCutP470_outer : vcCutP470.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP470_roots vcCutP470_bounds_eq vcCutP470_trees_ok

theorem vcCutP471_outer : vcCutP471.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP471_roots vcCutP471_bounds_eq vcCutP471_trees_ok

theorem vcCutP472_outer : vcCutP472.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP472_roots vcCutP472_bounds_eq vcCutP472_trees_ok

theorem vcCutP473_outer : vcCutP473.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP473_roots vcCutP473_bounds_eq vcCutP473_trees_ok

theorem vcCutP474_outer : vcCutP474.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP474_roots vcCutP474_bounds_eq vcCutP474_trees_ok

theorem vcCutP475_outer : vcCutP475.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP475_roots vcCutP475_bounds_eq vcCutP475_trees_ok

theorem vcCutP476_outer : vcCutP476.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP476_roots vcCutP476_bounds_eq vcCutP476_trees_ok

theorem vcCutP477_outer : vcCutP477.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP477_roots vcCutP477_bounds_eq vcCutP477_trees_ok

theorem vcCutP478_outer : vcCutP478.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP478_roots vcCutP478_bounds_eq vcCutP478_trees_ok

theorem vcCutP479_outer : vcCutP479.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP479_roots vcCutP479_bounds_eq vcCutP479_trees_ok

theorem vcCutWitnesses448 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints448.toList :=
  ⟨vcCutP448_outer,
   vcCutP449_outer,
   vcCutP450_outer,
   vcCutP451_outer,
   vcCutP452_outer,
   vcCutP453_outer,
   vcCutP454_outer,
   vcCutP455_outer,
   vcCutP456_outer,
   vcCutP457_outer,
   vcCutP458_outer,
   vcCutP459_outer,
   vcCutP460_outer,
   vcCutP461_outer,
   vcCutP462_outer,
   vcCutP463_outer,
   vcCutP464_outer,
   vcCutP465_outer,
   vcCutP466_outer,
   vcCutP467_outer,
   vcCutP468_outer,
   vcCutP469_outer,
   vcCutP470_outer,
   vcCutP471_outer,
   vcCutP472_outer,
   vcCutP473_outer,
   vcCutP474_outer,
   vcCutP475_outer,
   vcCutP476_outer,
   vcCutP477_outer,
   vcCutP478_outer,
   vcCutP479_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
