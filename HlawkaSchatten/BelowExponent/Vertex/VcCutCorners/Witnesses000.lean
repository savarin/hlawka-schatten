/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees000

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses000`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP000_outer : vcCutP000.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP000_roots vcCutP000_bounds_eq vcCutP000_trees_ok

theorem vcCutP001_outer : vcCutP001.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP001_roots vcCutP001_bounds_eq vcCutP001_trees_ok

theorem vcCutP002_outer : vcCutP002.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP002_roots vcCutP002_bounds_eq vcCutP002_trees_ok

theorem vcCutP003_outer : vcCutP003.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP003_roots vcCutP003_bounds_eq vcCutP003_trees_ok

theorem vcCutP004_outer : vcCutP004.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP004_roots vcCutP004_bounds_eq vcCutP004_trees_ok

theorem vcCutP005_outer : vcCutP005.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP005_roots vcCutP005_bounds_eq vcCutP005_trees_ok

theorem vcCutP006_outer : vcCutP006.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP006_roots vcCutP006_bounds_eq vcCutP006_trees_ok

theorem vcCutP007_outer : vcCutP007.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP007_roots vcCutP007_bounds_eq vcCutP007_trees_ok

theorem vcCutP008_outer : vcCutP008.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP008_roots vcCutP008_bounds_eq vcCutP008_trees_ok

theorem vcCutP009_outer : vcCutP009.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP009_roots vcCutP009_bounds_eq vcCutP009_trees_ok

theorem vcCutP010_outer : vcCutP010.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP010_roots vcCutP010_bounds_eq vcCutP010_trees_ok

theorem vcCutP011_outer : vcCutP011.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP011_roots vcCutP011_bounds_eq vcCutP011_trees_ok

theorem vcCutP012_outer : vcCutP012.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP012_roots vcCutP012_bounds_eq vcCutP012_trees_ok

theorem vcCutP013_outer : vcCutP013.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP013_roots vcCutP013_bounds_eq vcCutP013_trees_ok

theorem vcCutP014_outer : vcCutP014.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP014_roots vcCutP014_bounds_eq vcCutP014_trees_ok

theorem vcCutP015_outer : vcCutP015.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP015_roots vcCutP015_bounds_eq vcCutP015_trees_ok

theorem vcCutP016_outer : vcCutP016.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP016_roots vcCutP016_bounds_eq vcCutP016_trees_ok

theorem vcCutP017_outer : vcCutP017.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP017_roots vcCutP017_bounds_eq vcCutP017_trees_ok

theorem vcCutP018_outer : vcCutP018.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP018_roots vcCutP018_bounds_eq vcCutP018_trees_ok

theorem vcCutP019_outer : vcCutP019.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP019_roots vcCutP019_bounds_eq vcCutP019_trees_ok

theorem vcCutP020_outer : vcCutP020.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP020_roots vcCutP020_bounds_eq vcCutP020_trees_ok

theorem vcCutP021_outer : vcCutP021.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP021_roots vcCutP021_bounds_eq vcCutP021_trees_ok

theorem vcCutP022_outer : vcCutP022.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP022_roots vcCutP022_bounds_eq vcCutP022_trees_ok

theorem vcCutP023_outer : vcCutP023.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP023_roots vcCutP023_bounds_eq vcCutP023_trees_ok

theorem vcCutP024_outer : vcCutP024.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP024_roots vcCutP024_bounds_eq vcCutP024_trees_ok

theorem vcCutP025_outer : vcCutP025.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP025_roots vcCutP025_bounds_eq vcCutP025_trees_ok

theorem vcCutP026_outer : vcCutP026.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP026_roots vcCutP026_bounds_eq vcCutP026_trees_ok

theorem vcCutP027_outer : vcCutP027.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP027_roots vcCutP027_bounds_eq vcCutP027_trees_ok

theorem vcCutP028_outer : vcCutP028.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP028_roots vcCutP028_bounds_eq vcCutP028_trees_ok

theorem vcCutP029_outer : vcCutP029.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP029_roots vcCutP029_bounds_eq vcCutP029_trees_ok

theorem vcCutP030_outer : vcCutP030.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP030_roots vcCutP030_bounds_eq vcCutP030_trees_ok

theorem vcCutP031_outer : vcCutP031.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP031_roots vcCutP031_bounds_eq vcCutP031_trees_ok

theorem vcCutWitnesses000 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints000.toList :=
  ⟨vcCutP000_outer,
   vcCutP001_outer,
   vcCutP002_outer,
   vcCutP003_outer,
   vcCutP004_outer,
   vcCutP005_outer,
   vcCutP006_outer,
   vcCutP007_outer,
   vcCutP008_outer,
   vcCutP009_outer,
   vcCutP010_outer,
   vcCutP011_outer,
   vcCutP012_outer,
   vcCutP013_outer,
   vcCutP014_outer,
   vcCutP015_outer,
   vcCutP016_outer,
   vcCutP017_outer,
   vcCutP018_outer,
   vcCutP019_outer,
   vcCutP020_outer,
   vcCutP021_outer,
   vcCutP022_outer,
   vcCutP023_outer,
   vcCutP024_outer,
   vcCutP025_outer,
   vcCutP026_outer,
   vcCutP027_outer,
   vcCutP028_outer,
   vcCutP029_outer,
   vcCutP030_outer,
   vcCutP031_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
