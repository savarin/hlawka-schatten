/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees512

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses512`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP512_outer : vcCutP512.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP512_roots vcCutP512_bounds_eq vcCutP512_trees_ok

theorem vcCutP513_outer : vcCutP513.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP513_roots vcCutP513_bounds_eq vcCutP513_trees_ok

theorem vcCutP514_outer : vcCutP514.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP514_roots vcCutP514_bounds_eq vcCutP514_trees_ok

theorem vcCutP515_outer : vcCutP515.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP515_roots vcCutP515_bounds_eq vcCutP515_trees_ok

theorem vcCutP516_outer : vcCutP516.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP516_roots vcCutP516_bounds_eq vcCutP516_trees_ok

theorem vcCutP517_outer : vcCutP517.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP517_roots vcCutP517_bounds_eq vcCutP517_trees_ok

theorem vcCutP518_outer : vcCutP518.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP518_roots vcCutP518_bounds_eq vcCutP518_trees_ok

theorem vcCutP519_outer : vcCutP519.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP519_roots vcCutP519_bounds_eq vcCutP519_trees_ok

theorem vcCutP520_outer : vcCutP520.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP520_roots vcCutP520_bounds_eq vcCutP520_trees_ok

theorem vcCutP521_outer : vcCutP521.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP521_roots vcCutP521_bounds_eq vcCutP521_trees_ok

theorem vcCutP522_outer : vcCutP522.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP522_roots vcCutP522_bounds_eq vcCutP522_trees_ok

theorem vcCutP523_outer : vcCutP523.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP523_roots vcCutP523_bounds_eq vcCutP523_trees_ok

theorem vcCutP524_outer : vcCutP524.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP524_roots vcCutP524_bounds_eq vcCutP524_trees_ok

theorem vcCutP525_outer : vcCutP525.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP525_roots vcCutP525_bounds_eq vcCutP525_trees_ok

theorem vcCutP526_outer : vcCutP526.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP526_roots vcCutP526_bounds_eq vcCutP526_trees_ok

theorem vcCutP527_outer : vcCutP527.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP527_roots vcCutP527_bounds_eq vcCutP527_trees_ok

theorem vcCutP528_outer : vcCutP528.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP528_roots vcCutP528_bounds_eq vcCutP528_trees_ok

theorem vcCutP529_outer : vcCutP529.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP529_roots vcCutP529_bounds_eq vcCutP529_trees_ok

theorem vcCutP530_outer : vcCutP530.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP530_roots vcCutP530_bounds_eq vcCutP530_trees_ok

theorem vcCutP531_outer : vcCutP531.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP531_roots vcCutP531_bounds_eq vcCutP531_trees_ok

theorem vcCutP532_outer : vcCutP532.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP532_roots vcCutP532_bounds_eq vcCutP532_trees_ok

theorem vcCutP533_outer : vcCutP533.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP533_roots vcCutP533_bounds_eq vcCutP533_trees_ok

theorem vcCutP534_outer : vcCutP534.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP534_roots vcCutP534_bounds_eq vcCutP534_trees_ok

theorem vcCutP535_outer : vcCutP535.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP535_roots vcCutP535_bounds_eq vcCutP535_trees_ok

theorem vcCutP536_outer : vcCutP536.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP536_roots vcCutP536_bounds_eq vcCutP536_trees_ok

theorem vcCutP537_outer : vcCutP537.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP537_roots vcCutP537_bounds_eq vcCutP537_trees_ok

theorem vcCutP538_outer : vcCutP538.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP538_roots vcCutP538_bounds_eq vcCutP538_trees_ok

theorem vcCutP539_outer : vcCutP539.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP539_roots vcCutP539_bounds_eq vcCutP539_trees_ok

theorem vcCutP540_outer : vcCutP540.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP540_roots vcCutP540_bounds_eq vcCutP540_trees_ok

theorem vcCutP541_outer : vcCutP541.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP541_roots vcCutP541_bounds_eq vcCutP541_trees_ok

theorem vcCutP542_outer : vcCutP542.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP542_roots vcCutP542_bounds_eq vcCutP542_trees_ok

theorem vcCutP543_outer : vcCutP543.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP543_roots vcCutP543_bounds_eq vcCutP543_trees_ok

theorem vcCutWitnesses512 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints512.toList :=
  ⟨vcCutP512_outer,
   vcCutP513_outer,
   vcCutP514_outer,
   vcCutP515_outer,
   vcCutP516_outer,
   vcCutP517_outer,
   vcCutP518_outer,
   vcCutP519_outer,
   vcCutP520_outer,
   vcCutP521_outer,
   vcCutP522_outer,
   vcCutP523_outer,
   vcCutP524_outer,
   vcCutP525_outer,
   vcCutP526_outer,
   vcCutP527_outer,
   vcCutP528_outer,
   vcCutP529_outer,
   vcCutP530_outer,
   vcCutP531_outer,
   vcCutP532_outer,
   vcCutP533_outer,
   vcCutP534_outer,
   vcCutP535_outer,
   vcCutP536_outer,
   vcCutP537_outer,
   vcCutP538_outer,
   vcCutP539_outer,
   vcCutP540_outer,
   vcCutP541_outer,
   vcCutP542_outer,
   vcCutP543_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
