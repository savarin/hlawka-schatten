/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees480

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses480`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP480_outer : vcCutP480.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP480_roots vcCutP480_bounds_eq vcCutP480_trees_ok

theorem vcCutP481_outer : vcCutP481.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP481_roots vcCutP481_bounds_eq vcCutP481_trees_ok

theorem vcCutP482_outer : vcCutP482.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP482_roots vcCutP482_bounds_eq vcCutP482_trees_ok

theorem vcCutP483_outer : vcCutP483.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP483_roots vcCutP483_bounds_eq vcCutP483_trees_ok

theorem vcCutP484_outer : vcCutP484.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP484_roots vcCutP484_bounds_eq vcCutP484_trees_ok

theorem vcCutP485_outer : vcCutP485.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP485_roots vcCutP485_bounds_eq vcCutP485_trees_ok

theorem vcCutP486_outer : vcCutP486.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP486_roots vcCutP486_bounds_eq vcCutP486_trees_ok

theorem vcCutP487_outer : vcCutP487.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP487_roots vcCutP487_bounds_eq vcCutP487_trees_ok

theorem vcCutP488_outer : vcCutP488.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP488_roots vcCutP488_bounds_eq vcCutP488_trees_ok

theorem vcCutP489_outer : vcCutP489.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP489_roots vcCutP489_bounds_eq vcCutP489_trees_ok

theorem vcCutP490_outer : vcCutP490.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP490_roots vcCutP490_bounds_eq vcCutP490_trees_ok

theorem vcCutP491_outer : vcCutP491.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP491_roots vcCutP491_bounds_eq vcCutP491_trees_ok

theorem vcCutP492_outer : vcCutP492.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP492_roots vcCutP492_bounds_eq vcCutP492_trees_ok

theorem vcCutP493_outer : vcCutP493.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP493_roots vcCutP493_bounds_eq vcCutP493_trees_ok

theorem vcCutP494_outer : vcCutP494.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP494_roots vcCutP494_bounds_eq vcCutP494_trees_ok

theorem vcCutP495_outer : vcCutP495.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP495_roots vcCutP495_bounds_eq vcCutP495_trees_ok

theorem vcCutP496_outer : vcCutP496.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP496_roots vcCutP496_bounds_eq vcCutP496_trees_ok

theorem vcCutP497_outer : vcCutP497.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP497_roots vcCutP497_bounds_eq vcCutP497_trees_ok

theorem vcCutP498_outer : vcCutP498.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP498_roots vcCutP498_bounds_eq vcCutP498_trees_ok

theorem vcCutP499_outer : vcCutP499.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP499_roots vcCutP499_bounds_eq vcCutP499_trees_ok

theorem vcCutP500_outer : vcCutP500.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP500_roots vcCutP500_bounds_eq vcCutP500_trees_ok

theorem vcCutP501_outer : vcCutP501.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP501_roots vcCutP501_bounds_eq vcCutP501_trees_ok

theorem vcCutP502_outer : vcCutP502.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP502_roots vcCutP502_bounds_eq vcCutP502_trees_ok

theorem vcCutP503_outer : vcCutP503.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP503_roots vcCutP503_bounds_eq vcCutP503_trees_ok

theorem vcCutP504_outer : vcCutP504.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP504_roots vcCutP504_bounds_eq vcCutP504_trees_ok

theorem vcCutP505_outer : vcCutP505.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP505_roots vcCutP505_bounds_eq vcCutP505_trees_ok

theorem vcCutP506_outer : vcCutP506.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP506_roots vcCutP506_bounds_eq vcCutP506_trees_ok

theorem vcCutP507_outer : vcCutP507.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP507_roots vcCutP507_bounds_eq vcCutP507_trees_ok

theorem vcCutP508_outer : vcCutP508.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP508_roots vcCutP508_bounds_eq vcCutP508_trees_ok

theorem vcCutP509_outer : vcCutP509.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP509_roots vcCutP509_bounds_eq vcCutP509_trees_ok

theorem vcCutP510_outer : vcCutP510.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP510_roots vcCutP510_bounds_eq vcCutP510_trees_ok

theorem vcCutP511_outer : vcCutP511.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP511_roots vcCutP511_bounds_eq vcCutP511_trees_ok

theorem vcCutWitnesses480 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints480.toList :=
  ⟨vcCutP480_outer,
   vcCutP481_outer,
   vcCutP482_outer,
   vcCutP483_outer,
   vcCutP484_outer,
   vcCutP485_outer,
   vcCutP486_outer,
   vcCutP487_outer,
   vcCutP488_outer,
   vcCutP489_outer,
   vcCutP490_outer,
   vcCutP491_outer,
   vcCutP492_outer,
   vcCutP493_outer,
   vcCutP494_outer,
   vcCutP495_outer,
   vcCutP496_outer,
   vcCutP497_outer,
   vcCutP498_outer,
   vcCutP499_outer,
   vcCutP500_outer,
   vcCutP501_outer,
   vcCutP502_outer,
   vcCutP503_outer,
   vcCutP504_outer,
   vcCutP505_outer,
   vcCutP506_outer,
   vcCutP507_outer,
   vcCutP508_outer,
   vcCutP509_outer,
   vcCutP510_outer,
   vcCutP511_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
