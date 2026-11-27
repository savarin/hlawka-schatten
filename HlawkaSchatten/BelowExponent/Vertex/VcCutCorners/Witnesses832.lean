/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees832

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses832`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP832_outer : vcCutP832.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP832_roots vcCutP832_bounds_eq vcCutP832_trees_ok

theorem vcCutP833_outer : vcCutP833.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP833_roots vcCutP833_bounds_eq vcCutP833_trees_ok

theorem vcCutP834_outer : vcCutP834.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP834_roots vcCutP834_bounds_eq vcCutP834_trees_ok

theorem vcCutP835_outer : vcCutP835.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP835_roots vcCutP835_bounds_eq vcCutP835_trees_ok

theorem vcCutP836_outer : vcCutP836.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP836_roots vcCutP836_bounds_eq vcCutP836_trees_ok

theorem vcCutP837_outer : vcCutP837.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP837_roots vcCutP837_bounds_eq vcCutP837_trees_ok

theorem vcCutP838_outer : vcCutP838.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP838_roots vcCutP838_bounds_eq vcCutP838_trees_ok

theorem vcCutP839_outer : vcCutP839.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP839_roots vcCutP839_bounds_eq vcCutP839_trees_ok

theorem vcCutP840_outer : vcCutP840.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP840_roots vcCutP840_bounds_eq vcCutP840_trees_ok

theorem vcCutP841_outer : vcCutP841.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP841_roots vcCutP841_bounds_eq vcCutP841_trees_ok

theorem vcCutP842_outer : vcCutP842.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP842_roots vcCutP842_bounds_eq vcCutP842_trees_ok

theorem vcCutP843_outer : vcCutP843.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP843_roots vcCutP843_bounds_eq vcCutP843_trees_ok

theorem vcCutP844_outer : vcCutP844.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP844_roots vcCutP844_bounds_eq vcCutP844_trees_ok

theorem vcCutP845_outer : vcCutP845.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP845_roots vcCutP845_bounds_eq vcCutP845_trees_ok

theorem vcCutP846_outer : vcCutP846.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP846_roots vcCutP846_bounds_eq vcCutP846_trees_ok

theorem vcCutP847_outer : vcCutP847.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP847_roots vcCutP847_bounds_eq vcCutP847_trees_ok

theorem vcCutP848_outer : vcCutP848.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP848_roots vcCutP848_bounds_eq vcCutP848_trees_ok

theorem vcCutP849_outer : vcCutP849.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP849_roots vcCutP849_bounds_eq vcCutP849_trees_ok

theorem vcCutP850_outer : vcCutP850.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP850_roots vcCutP850_bounds_eq vcCutP850_trees_ok

theorem vcCutP851_outer : vcCutP851.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP851_roots vcCutP851_bounds_eq vcCutP851_trees_ok

theorem vcCutP852_outer : vcCutP852.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP852_roots vcCutP852_bounds_eq vcCutP852_trees_ok

theorem vcCutP853_outer : vcCutP853.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP853_roots vcCutP853_bounds_eq vcCutP853_trees_ok

theorem vcCutP854_outer : vcCutP854.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP854_roots vcCutP854_bounds_eq vcCutP854_trees_ok

theorem vcCutP855_outer : vcCutP855.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP855_roots vcCutP855_bounds_eq vcCutP855_trees_ok

theorem vcCutP856_outer : vcCutP856.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP856_roots vcCutP856_bounds_eq vcCutP856_trees_ok

theorem vcCutP857_outer : vcCutP857.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP857_roots vcCutP857_bounds_eq vcCutP857_trees_ok

theorem vcCutP858_outer : vcCutP858.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP858_roots vcCutP858_bounds_eq vcCutP858_trees_ok

theorem vcCutP859_outer : vcCutP859.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP859_roots vcCutP859_bounds_eq vcCutP859_trees_ok

theorem vcCutP860_outer : vcCutP860.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP860_roots vcCutP860_bounds_eq vcCutP860_trees_ok

theorem vcCutP861_outer : vcCutP861.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP861_roots vcCutP861_bounds_eq vcCutP861_trees_ok

theorem vcCutP862_outer : vcCutP862.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP862_roots vcCutP862_bounds_eq vcCutP862_trees_ok

theorem vcCutP863_outer : vcCutP863.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP863_roots vcCutP863_bounds_eq vcCutP863_trees_ok

theorem vcCutWitnesses832 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints832.toList :=
  ⟨vcCutP832_outer,
   vcCutP833_outer,
   vcCutP834_outer,
   vcCutP835_outer,
   vcCutP836_outer,
   vcCutP837_outer,
   vcCutP838_outer,
   vcCutP839_outer,
   vcCutP840_outer,
   vcCutP841_outer,
   vcCutP842_outer,
   vcCutP843_outer,
   vcCutP844_outer,
   vcCutP845_outer,
   vcCutP846_outer,
   vcCutP847_outer,
   vcCutP848_outer,
   vcCutP849_outer,
   vcCutP850_outer,
   vcCutP851_outer,
   vcCutP852_outer,
   vcCutP853_outer,
   vcCutP854_outer,
   vcCutP855_outer,
   vcCutP856_outer,
   vcCutP857_outer,
   vcCutP858_outer,
   vcCutP859_outer,
   vcCutP860_outer,
   vcCutP861_outer,
   vcCutP862_outer,
   vcCutP863_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
