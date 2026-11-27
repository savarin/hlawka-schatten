/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees320

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses320`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP320_outer : vcCutP320.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP320_roots vcCutP320_bounds_eq vcCutP320_trees_ok

theorem vcCutP321_outer : vcCutP321.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP321_roots vcCutP321_bounds_eq vcCutP321_trees_ok

theorem vcCutP322_outer : vcCutP322.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP322_roots vcCutP322_bounds_eq vcCutP322_trees_ok

theorem vcCutP323_outer : vcCutP323.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP323_roots vcCutP323_bounds_eq vcCutP323_trees_ok

theorem vcCutP324_outer : vcCutP324.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP324_roots vcCutP324_bounds_eq vcCutP324_trees_ok

theorem vcCutP325_outer : vcCutP325.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP325_roots vcCutP325_bounds_eq vcCutP325_trees_ok

theorem vcCutP326_outer : vcCutP326.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP326_roots vcCutP326_bounds_eq vcCutP326_trees_ok

theorem vcCutP327_outer : vcCutP327.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP327_roots vcCutP327_bounds_eq vcCutP327_trees_ok

theorem vcCutP328_outer : vcCutP328.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP328_roots vcCutP328_bounds_eq vcCutP328_trees_ok

theorem vcCutP329_outer : vcCutP329.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP329_roots vcCutP329_bounds_eq vcCutP329_trees_ok

theorem vcCutP330_outer : vcCutP330.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP330_roots vcCutP330_bounds_eq vcCutP330_trees_ok

theorem vcCutP331_outer : vcCutP331.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP331_roots vcCutP331_bounds_eq vcCutP331_trees_ok

theorem vcCutP332_outer : vcCutP332.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP332_roots vcCutP332_bounds_eq vcCutP332_trees_ok

theorem vcCutP333_outer : vcCutP333.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP333_roots vcCutP333_bounds_eq vcCutP333_trees_ok

theorem vcCutP334_outer : vcCutP334.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP334_roots vcCutP334_bounds_eq vcCutP334_trees_ok

theorem vcCutP335_outer : vcCutP335.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP335_roots vcCutP335_bounds_eq vcCutP335_trees_ok

theorem vcCutP336_outer : vcCutP336.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP336_roots vcCutP336_bounds_eq vcCutP336_trees_ok

theorem vcCutP337_outer : vcCutP337.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP337_roots vcCutP337_bounds_eq vcCutP337_trees_ok

theorem vcCutP338_outer : vcCutP338.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP338_roots vcCutP338_bounds_eq vcCutP338_trees_ok

theorem vcCutP339_outer : vcCutP339.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP339_roots vcCutP339_bounds_eq vcCutP339_trees_ok

theorem vcCutP340_outer : vcCutP340.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP340_roots vcCutP340_bounds_eq vcCutP340_trees_ok

theorem vcCutP341_outer : vcCutP341.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP341_roots vcCutP341_bounds_eq vcCutP341_trees_ok

theorem vcCutP342_outer : vcCutP342.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP342_roots vcCutP342_bounds_eq vcCutP342_trees_ok

theorem vcCutP343_outer : vcCutP343.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP343_roots vcCutP343_bounds_eq vcCutP343_trees_ok

theorem vcCutP344_outer : vcCutP344.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP344_roots vcCutP344_bounds_eq vcCutP344_trees_ok

theorem vcCutP345_outer : vcCutP345.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP345_roots vcCutP345_bounds_eq vcCutP345_trees_ok

theorem vcCutP346_outer : vcCutP346.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP346_roots vcCutP346_bounds_eq vcCutP346_trees_ok

theorem vcCutP347_outer : vcCutP347.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP347_roots vcCutP347_bounds_eq vcCutP347_trees_ok

theorem vcCutP348_outer : vcCutP348.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP348_roots vcCutP348_bounds_eq vcCutP348_trees_ok

theorem vcCutP349_outer : vcCutP349.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP349_roots vcCutP349_bounds_eq vcCutP349_trees_ok

theorem vcCutP350_outer : vcCutP350.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP350_roots vcCutP350_bounds_eq vcCutP350_trees_ok

theorem vcCutP351_outer : vcCutP351.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP351_roots vcCutP351_bounds_eq vcCutP351_trees_ok

theorem vcCutWitnesses320 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints320.toList :=
  ⟨vcCutP320_outer,
   vcCutP321_outer,
   vcCutP322_outer,
   vcCutP323_outer,
   vcCutP324_outer,
   vcCutP325_outer,
   vcCutP326_outer,
   vcCutP327_outer,
   vcCutP328_outer,
   vcCutP329_outer,
   vcCutP330_outer,
   vcCutP331_outer,
   vcCutP332_outer,
   vcCutP333_outer,
   vcCutP334_outer,
   vcCutP335_outer,
   vcCutP336_outer,
   vcCutP337_outer,
   vcCutP338_outer,
   vcCutP339_outer,
   vcCutP340_outer,
   vcCutP341_outer,
   vcCutP342_outer,
   vcCutP343_outer,
   vcCutP344_outer,
   vcCutP345_outer,
   vcCutP346_outer,
   vcCutP347_outer,
   vcCutP348_outer,
   vcCutP349_outer,
   vcCutP350_outer,
   vcCutP351_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
