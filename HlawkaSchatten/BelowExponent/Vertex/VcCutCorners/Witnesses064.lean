/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees064

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses064`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP064_outer : vcCutP064.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP064_roots vcCutP064_bounds_eq vcCutP064_trees_ok

theorem vcCutP065_outer : vcCutP065.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP065_roots vcCutP065_bounds_eq vcCutP065_trees_ok

theorem vcCutP066_outer : vcCutP066.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP066_roots vcCutP066_bounds_eq vcCutP066_trees_ok

theorem vcCutP067_outer : vcCutP067.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP067_roots vcCutP067_bounds_eq vcCutP067_trees_ok

theorem vcCutP068_outer : vcCutP068.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP068_roots vcCutP068_bounds_eq vcCutP068_trees_ok

theorem vcCutP069_outer : vcCutP069.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP069_roots vcCutP069_bounds_eq vcCutP069_trees_ok

theorem vcCutP070_outer : vcCutP070.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP070_roots vcCutP070_bounds_eq vcCutP070_trees_ok

theorem vcCutP071_outer : vcCutP071.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP071_roots vcCutP071_bounds_eq vcCutP071_trees_ok

theorem vcCutP072_outer : vcCutP072.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP072_roots vcCutP072_bounds_eq vcCutP072_trees_ok

theorem vcCutP073_outer : vcCutP073.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP073_roots vcCutP073_bounds_eq vcCutP073_trees_ok

theorem vcCutP074_outer : vcCutP074.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP074_roots vcCutP074_bounds_eq vcCutP074_trees_ok

theorem vcCutP075_outer : vcCutP075.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP075_roots vcCutP075_bounds_eq vcCutP075_trees_ok

theorem vcCutP076_outer : vcCutP076.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP076_roots vcCutP076_bounds_eq vcCutP076_trees_ok

theorem vcCutP077_outer : vcCutP077.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP077_roots vcCutP077_bounds_eq vcCutP077_trees_ok

theorem vcCutP078_outer : vcCutP078.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP078_roots vcCutP078_bounds_eq vcCutP078_trees_ok

theorem vcCutP079_outer : vcCutP079.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP079_roots vcCutP079_bounds_eq vcCutP079_trees_ok

theorem vcCutP080_outer : vcCutP080.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP080_roots vcCutP080_bounds_eq vcCutP080_trees_ok

theorem vcCutP081_outer : vcCutP081.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP081_roots vcCutP081_bounds_eq vcCutP081_trees_ok

theorem vcCutP082_outer : vcCutP082.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP082_roots vcCutP082_bounds_eq vcCutP082_trees_ok

theorem vcCutP083_outer : vcCutP083.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP083_roots vcCutP083_bounds_eq vcCutP083_trees_ok

theorem vcCutP084_outer : vcCutP084.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP084_roots vcCutP084_bounds_eq vcCutP084_trees_ok

theorem vcCutP085_outer : vcCutP085.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP085_roots vcCutP085_bounds_eq vcCutP085_trees_ok

theorem vcCutP086_outer : vcCutP086.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP086_roots vcCutP086_bounds_eq vcCutP086_trees_ok

theorem vcCutP087_outer : vcCutP087.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP087_roots vcCutP087_bounds_eq vcCutP087_trees_ok

theorem vcCutP088_outer : vcCutP088.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP088_roots vcCutP088_bounds_eq vcCutP088_trees_ok

theorem vcCutP089_outer : vcCutP089.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP089_roots vcCutP089_bounds_eq vcCutP089_trees_ok

theorem vcCutP090_outer : vcCutP090.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP090_roots vcCutP090_bounds_eq vcCutP090_trees_ok

theorem vcCutP091_outer : vcCutP091.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP091_roots vcCutP091_bounds_eq vcCutP091_trees_ok

theorem vcCutP092_outer : vcCutP092.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP092_roots vcCutP092_bounds_eq vcCutP092_trees_ok

theorem vcCutP093_outer : vcCutP093.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP093_roots vcCutP093_bounds_eq vcCutP093_trees_ok

theorem vcCutP094_outer : vcCutP094.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP094_roots vcCutP094_bounds_eq vcCutP094_trees_ok

theorem vcCutP095_outer : vcCutP095.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP095_roots vcCutP095_bounds_eq vcCutP095_trees_ok

theorem vcCutWitnesses064 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints064.toList :=
  ⟨vcCutP064_outer,
   vcCutP065_outer,
   vcCutP066_outer,
   vcCutP067_outer,
   vcCutP068_outer,
   vcCutP069_outer,
   vcCutP070_outer,
   vcCutP071_outer,
   vcCutP072_outer,
   vcCutP073_outer,
   vcCutP074_outer,
   vcCutP075_outer,
   vcCutP076_outer,
   vcCutP077_outer,
   vcCutP078_outer,
   vcCutP079_outer,
   vcCutP080_outer,
   vcCutP081_outer,
   vcCutP082_outer,
   vcCutP083_outer,
   vcCutP084_outer,
   vcCutP085_outer,
   vcCutP086_outer,
   vcCutP087_outer,
   vcCutP088_outer,
   vcCutP089_outer,
   vcCutP090_outer,
   vcCutP091_outer,
   vcCutP092_outer,
   vcCutP093_outer,
   vcCutP094_outer,
   vcCutP095_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
