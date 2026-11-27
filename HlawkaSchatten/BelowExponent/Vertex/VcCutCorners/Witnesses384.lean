/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees384

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses384`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP384_outer : vcCutP384.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP384_roots vcCutP384_bounds_eq vcCutP384_trees_ok

theorem vcCutP385_outer : vcCutP385.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP385_roots vcCutP385_bounds_eq vcCutP385_trees_ok

theorem vcCutP386_outer : vcCutP386.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP386_roots vcCutP386_bounds_eq vcCutP386_trees_ok

theorem vcCutP387_outer : vcCutP387.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP387_roots vcCutP387_bounds_eq vcCutP387_trees_ok

theorem vcCutP388_outer : vcCutP388.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP388_roots vcCutP388_bounds_eq vcCutP388_trees_ok

theorem vcCutP389_outer : vcCutP389.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP389_roots vcCutP389_bounds_eq vcCutP389_trees_ok

theorem vcCutP390_outer : vcCutP390.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP390_roots vcCutP390_bounds_eq vcCutP390_trees_ok

theorem vcCutP391_outer : vcCutP391.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP391_roots vcCutP391_bounds_eq vcCutP391_trees_ok

theorem vcCutP392_outer : vcCutP392.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP392_roots vcCutP392_bounds_eq vcCutP392_trees_ok

theorem vcCutP393_outer : vcCutP393.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP393_roots vcCutP393_bounds_eq vcCutP393_trees_ok

theorem vcCutP394_outer : vcCutP394.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP394_roots vcCutP394_bounds_eq vcCutP394_trees_ok

theorem vcCutP395_outer : vcCutP395.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP395_roots vcCutP395_bounds_eq vcCutP395_trees_ok

theorem vcCutP396_outer : vcCutP396.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP396_roots vcCutP396_bounds_eq vcCutP396_trees_ok

theorem vcCutP397_outer : vcCutP397.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP397_roots vcCutP397_bounds_eq vcCutP397_trees_ok

theorem vcCutP398_outer : vcCutP398.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP398_roots vcCutP398_bounds_eq vcCutP398_trees_ok

theorem vcCutP399_outer : vcCutP399.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP399_roots vcCutP399_bounds_eq vcCutP399_trees_ok

theorem vcCutP400_outer : vcCutP400.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP400_roots vcCutP400_bounds_eq vcCutP400_trees_ok

theorem vcCutP401_outer : vcCutP401.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP401_roots vcCutP401_bounds_eq vcCutP401_trees_ok

theorem vcCutP402_outer : vcCutP402.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP402_roots vcCutP402_bounds_eq vcCutP402_trees_ok

theorem vcCutP403_outer : vcCutP403.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP403_roots vcCutP403_bounds_eq vcCutP403_trees_ok

theorem vcCutP404_outer : vcCutP404.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP404_roots vcCutP404_bounds_eq vcCutP404_trees_ok

theorem vcCutP405_outer : vcCutP405.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP405_roots vcCutP405_bounds_eq vcCutP405_trees_ok

theorem vcCutP406_outer : vcCutP406.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP406_roots vcCutP406_bounds_eq vcCutP406_trees_ok

theorem vcCutP407_outer : vcCutP407.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP407_roots vcCutP407_bounds_eq vcCutP407_trees_ok

theorem vcCutP408_outer : vcCutP408.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP408_roots vcCutP408_bounds_eq vcCutP408_trees_ok

theorem vcCutP409_outer : vcCutP409.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP409_roots vcCutP409_bounds_eq vcCutP409_trees_ok

theorem vcCutP410_outer : vcCutP410.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP410_roots vcCutP410_bounds_eq vcCutP410_trees_ok

theorem vcCutP411_outer : vcCutP411.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP411_roots vcCutP411_bounds_eq vcCutP411_trees_ok

theorem vcCutP412_outer : vcCutP412.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP412_roots vcCutP412_bounds_eq vcCutP412_trees_ok

theorem vcCutP413_outer : vcCutP413.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP413_roots vcCutP413_bounds_eq vcCutP413_trees_ok

theorem vcCutP414_outer : vcCutP414.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP414_roots vcCutP414_bounds_eq vcCutP414_trees_ok

theorem vcCutP415_outer : vcCutP415.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP415_roots vcCutP415_bounds_eq vcCutP415_trees_ok

theorem vcCutWitnesses384 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints384.toList :=
  ⟨vcCutP384_outer,
   vcCutP385_outer,
   vcCutP386_outer,
   vcCutP387_outer,
   vcCutP388_outer,
   vcCutP389_outer,
   vcCutP390_outer,
   vcCutP391_outer,
   vcCutP392_outer,
   vcCutP393_outer,
   vcCutP394_outer,
   vcCutP395_outer,
   vcCutP396_outer,
   vcCutP397_outer,
   vcCutP398_outer,
   vcCutP399_outer,
   vcCutP400_outer,
   vcCutP401_outer,
   vcCutP402_outer,
   vcCutP403_outer,
   vcCutP404_outer,
   vcCutP405_outer,
   vcCutP406_outer,
   vcCutP407_outer,
   vcCutP408_outer,
   vcCutP409_outer,
   vcCutP410_outer,
   vcCutP411_outer,
   vcCutP412_outer,
   vcCutP413_outer,
   vcCutP414_outer,
   vcCutP415_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
