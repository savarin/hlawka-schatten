/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism1Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism2Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism3Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism4Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism5Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism6Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism7Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism8Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism9Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism10Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism11Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism12Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism13Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism14Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism15Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism16Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism17Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism18Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism19Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism20Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism21Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism22Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F1Prism23Real

/-! Archived facet prism certificate data: `F1Root`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

private theorem f1RowsRoot000 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 0 1) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 0 1) = f1Archived1Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived1Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived1_rows

private theorem f1RowsRoot00100000 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 0 2) 1 2) 0 2) 1 2) 0 2) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 0 2) 1 2) 0 2) 1 2) 0 2) = f1Archived2Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived2Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived2_rows

private theorem f1RowsRoot00100001 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 0 2) 1 2) 0 2) 1 2) 2 0) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 0 2) 1 2) 0 2) 1 2) 2 0) = f1Archived3Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived3Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived3_rows

private theorem f1RowsRoot0010000 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 0 2) 1 2) 0 2) 1 2) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 2) (by decide) f1RowsRoot00100000 f1RowsRoot00100001

private theorem f1RowsRoot0010001 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 0 2) 1 2) 0 2) 2 1) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 0 2) 1 2) 0 2) 2 1) = f1Archived4Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived4Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived4_rows

private theorem f1RowsRoot001000 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 0 2) 1 2) 0 2) := by
  exact facetArchiveTriangle_of_split (i := 1) (j := 2) (by decide) f1RowsRoot0010000 f1RowsRoot0010001

private theorem f1RowsRoot001001 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 0 2) 1 2) 2 0) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 0 2) 1 2) 2 0) = f1Archived5Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived5Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived5_rows

private theorem f1RowsRoot00100 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 0 2) 1 2) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 2) (by decide) f1RowsRoot001000 f1RowsRoot001001

private theorem f1RowsRoot00101 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 0 2) 2 1) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 0 2) 2 1) = f1Archived6Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived6Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived6_rows

private theorem f1RowsRoot0010 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 0 2) := by
  exact facetArchiveTriangle_of_split (i := 1) (j := 2) (by decide) f1RowsRoot00100 f1RowsRoot00101

private theorem f1RowsRoot00110 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 2 0) 0 1) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 2 0) 0 1) = f1Archived7Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived7Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived7_rows

private theorem f1RowsRoot001110 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 2 0) 1 0) 0 2) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 2 0) 1 0) 0 2) = f1Archived8Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived8Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived8_rows

private theorem f1RowsRoot001111 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 2 0) 1 0) 2 0) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 2 0) 1 0) 2 0) = f1Archived9Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived9Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived9_rows

private theorem f1RowsRoot00111 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 2 0) 1 0) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 2) (by decide) f1RowsRoot001110 f1RowsRoot001111

private theorem f1RowsRoot0011 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) 2 0) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 1) (by decide) f1RowsRoot00110 f1RowsRoot00111

private theorem f1RowsRoot001 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) 1 0) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 2) (by decide) f1RowsRoot0010 f1RowsRoot0011

private theorem f1RowsRoot00 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 0 2) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 1) (by decide) f1RowsRoot000 f1RowsRoot001

private theorem f1RowsRoot0100 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 2 0) 0 1) 1 2) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 2 0) 0 1) 1 2) = f1Archived10Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived10Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived10_rows

private theorem f1RowsRoot0101 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 2 0) 0 1) 2 1) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 2 0) 0 1) 2 1) = f1Archived11Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived11Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived11_rows

private theorem f1RowsRoot010 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 2 0) 0 1) := by
  exact facetArchiveTriangle_of_split (i := 1) (j := 2) (by decide) f1RowsRoot0100 f1RowsRoot0101

private theorem f1RowsRoot0110 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 2 0) 1 0) 0 2) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 2 0) 1 0) 0 2) = f1Archived12Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived12Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived12_rows

private theorem f1RowsRoot01110 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 2 0) 1 0) 2 0) 0 1) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 2 0) 1 0) 2 0) 0 1) = f1Archived13Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived13Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived13_rows

private theorem f1RowsRoot01111 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 2 0) 1 0) 2 0) 1 0) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 2 0) 1 0) 2 0) 1 0) = f1Archived14Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived14Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived14_rows

private theorem f1RowsRoot0111 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 2 0) 1 0) 2 0) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 1) (by decide) f1RowsRoot01110 f1RowsRoot01111

private theorem f1RowsRoot011 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 2 0) 1 0) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 2) (by decide) f1RowsRoot0110 f1RowsRoot0111

private theorem f1RowsRoot01 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 0 2) 2 0) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 1) (by decide) f1RowsRoot010 f1RowsRoot011

private theorem f1RowsRoot0 : FacetArchiveTriangle criticalQ (g2SplitTriangle (facetArchiveRoot 1) 0 2) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 2) (by decide) f1RowsRoot00 f1RowsRoot01

private theorem f1RowsRoot1000 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 0 1) 1 2) 1 2) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 0 1) 1 2) 1 2) = f1Archived15Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived15Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived15_rows

private theorem f1RowsRoot1001 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 0 1) 1 2) 2 1) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 0 1) 1 2) 2 1) = f1Archived16Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived16Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived16_rows

private theorem f1RowsRoot100 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 0 1) 1 2) := by
  exact facetArchiveTriangle_of_split (i := 1) (j := 2) (by decide) f1RowsRoot1000 f1RowsRoot1001

private theorem f1RowsRoot1010 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 0 1) 2 1) 0 1) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 0 1) 2 1) 0 1) = f1Archived17Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived17Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived17_rows

private theorem f1RowsRoot1011 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 0 1) 2 1) 1 0) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 0 1) 2 1) 1 0) = f1Archived18Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived18Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived18_rows

private theorem f1RowsRoot101 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 0 1) 2 1) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 1) (by decide) f1RowsRoot1010 f1RowsRoot1011

private theorem f1RowsRoot10 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 0 1) := by
  exact facetArchiveTriangle_of_split (i := 1) (j := 2) (by decide) f1RowsRoot100 f1RowsRoot101

private theorem f1RowsRoot110 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 1 0) 0 2) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 1 0) 0 2) = f1Archived19Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived19Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived19_rows

private theorem f1RowsRoot1110 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 1 0) 2 0) 0 1) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 1 0) 2 0) 0 1) = f1Archived20Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived20Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived20_rows

private theorem f1RowsRoot11110 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 1 0) 2 0) 1 0) 0 2) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 1 0) 2 0) 1 0) 0 2) = f1Archived21Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived21Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived21_rows

private theorem f1RowsRoot111110 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 1 0) 2 0) 1 0) 2 0) 0 1) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 1 0) 2 0) 1 0) 2 0) 0 1) = f1Archived22Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived22Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived22_rows

private theorem f1RowsRoot111111 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 1 0) 2 0) 1 0) 2 0) 1 0) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 1 0) 2 0) 1 0) 2 0) 1 0) = f1Archived23Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f1Archived23Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f1Archived23_rows

private theorem f1RowsRoot11111 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 1 0) 2 0) 1 0) 2 0) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 1) (by decide) f1RowsRoot111110 f1RowsRoot111111

private theorem f1RowsRoot1111 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 1 0) 2 0) 1 0) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 2) (by decide) f1RowsRoot11110 f1RowsRoot11111

private theorem f1RowsRoot111 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 1 0) 2 0) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 1) (by decide) f1RowsRoot1110 f1RowsRoot1111

private theorem f1RowsRoot11 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 1) 2 0) 1 0) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 2) (by decide) f1RowsRoot110 f1RowsRoot111

private theorem f1RowsRoot1 : FacetArchiveTriangle criticalQ (g2SplitTriangle (facetArchiveRoot 1) 2 0) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 1) (by decide) f1RowsRoot10 f1RowsRoot11

theorem f1RowsRoot : FacetArchiveTriangle criticalQ (facetArchiveRoot 1) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 2) (by decide) f1RowsRoot0 f1RowsRoot1

end HlawkaSchatten.BelowExponent.FacetNumeric
