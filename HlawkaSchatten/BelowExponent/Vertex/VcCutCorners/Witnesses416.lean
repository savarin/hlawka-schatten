/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeProof
public import HlawkaSchatten.BelowExponent.Vertex.VcCutCorners.Trees416

/-! Checked corner data shared by the vertex middle and band regions: `Witnesses416`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

set_option maxRecDepth 10000

theorem vcCutP416_outer : vcCutP416.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP416_roots vcCutP416_bounds_eq vcCutP416_trees_ok

theorem vcCutP417_outer : vcCutP417.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP417_roots vcCutP417_bounds_eq vcCutP417_trees_ok

theorem vcCutP418_outer : vcCutP418.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP418_roots vcCutP418_bounds_eq vcCutP418_trees_ok

theorem vcCutP419_outer : vcCutP419.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP419_roots vcCutP419_bounds_eq vcCutP419_trees_ok

theorem vcCutP420_outer : vcCutP420.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP420_roots vcCutP420_bounds_eq vcCutP420_trees_ok

theorem vcCutP421_outer : vcCutP421.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP421_roots vcCutP421_bounds_eq vcCutP421_trees_ok

theorem vcCutP422_outer : vcCutP422.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP422_roots vcCutP422_bounds_eq vcCutP422_trees_ok

theorem vcCutP423_outer : vcCutP423.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP423_roots vcCutP423_bounds_eq vcCutP423_trees_ok

theorem vcCutP424_outer : vcCutP424.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP424_roots vcCutP424_bounds_eq vcCutP424_trees_ok

theorem vcCutP425_outer : vcCutP425.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP425_roots vcCutP425_bounds_eq vcCutP425_trees_ok

theorem vcCutP426_outer : vcCutP426.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP426_roots vcCutP426_bounds_eq vcCutP426_trees_ok

theorem vcCutP427_outer : vcCutP427.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP427_roots vcCutP427_bounds_eq vcCutP427_trees_ok

theorem vcCutP428_outer : vcCutP428.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP428_roots vcCutP428_bounds_eq vcCutP428_trees_ok

theorem vcCutP429_outer : vcCutP429.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP429_roots vcCutP429_bounds_eq vcCutP429_trees_ok

theorem vcCutP430_outer : vcCutP430.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP430_roots vcCutP430_bounds_eq vcCutP430_trees_ok

theorem vcCutP431_outer : vcCutP431.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP431_roots vcCutP431_bounds_eq vcCutP431_trees_ok

theorem vcCutP432_outer : vcCutP432.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP432_roots vcCutP432_bounds_eq vcCutP432_trees_ok

theorem vcCutP433_outer : vcCutP433.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP433_roots vcCutP433_bounds_eq vcCutP433_trees_ok

theorem vcCutP434_outer : vcCutP434.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP434_roots vcCutP434_bounds_eq vcCutP434_trees_ok

theorem vcCutP435_outer : vcCutP435.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP435_roots vcCutP435_bounds_eq vcCutP435_trees_ok

theorem vcCutP436_outer : vcCutP436.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP436_roots vcCutP436_bounds_eq vcCutP436_trees_ok

theorem vcCutP437_outer : vcCutP437.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP437_roots vcCutP437_bounds_eq vcCutP437_trees_ok

theorem vcCutP438_outer : vcCutP438.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP438_roots vcCutP438_bounds_eq vcCutP438_trees_ok

theorem vcCutP439_outer : vcCutP439.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP439_roots vcCutP439_bounds_eq vcCutP439_trees_ok

theorem vcCutP440_outer : vcCutP440.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP440_roots vcCutP440_bounds_eq vcCutP440_trees_ok

theorem vcCutP441_outer : vcCutP441.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP441_roots vcCutP441_bounds_eq vcCutP441_trees_ok

theorem vcCutP442_outer : vcCutP442.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP442_roots vcCutP442_bounds_eq vcCutP442_trees_ok

theorem vcCutP443_outer : vcCutP443.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP443_roots vcCutP443_bounds_eq vcCutP443_trees_ok

theorem vcCutP444_outer : vcCutP444.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP444_roots vcCutP444_bounds_eq vcCutP444_trees_ok

theorem vcCutP445_outer : vcCutP445.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP445_roots vcCutP445_bounds_eq vcCutP445_trees_ok

theorem vcCutP446_outer : vcCutP446.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP446_roots vcCutP446_bounds_eq vcCutP446_trees_ok

theorem vcCutP447_outer : vcCutP447.ValidFor (fun _ => True) :=
  vcOuterValid_of_treesOK vcCutP447_roots vcCutP447_bounds_eq vcCutP447_trees_ok

theorem vcCutWitnesses416 :
    SideCornerEntriesOK (fun _ => True) vcCutPoints416.toList :=
  ⟨vcCutP416_outer,
   vcCutP417_outer,
   vcCutP418_outer,
   vcCutP419_outer,
   vcCutP420_outer,
   vcCutP421_outer,
   vcCutP422_outer,
   vcCutP423_outer,
   vcCutP424_outer,
   vcCutP425_outer,
   vcCutP426_outer,
   vcCutP427_outer,
   vcCutP428_outer,
   vcCutP429_outer,
   vcCutP430_outer,
   vcCutP431_outer,
   vcCutP432_outer,
   vcCutP433_outer,
   vcCutP434_outer,
   vcCutP435_outer,
   vcCutP436_outer,
   vcCutP437_outer,
   vcCutP438_outer,
   vcCutP439_outer,
   vcCutP440_outer,
   vcCutP441_outer,
   vcCutP442_outer,
   vcCutP443_outer,
   vcCutP444_outer,
   vcCutP445_outer,
   vcCutP446_outer,
   vcCutP447_outer, True.intro⟩

end HlawkaSchatten.BelowExponent.Vertex
