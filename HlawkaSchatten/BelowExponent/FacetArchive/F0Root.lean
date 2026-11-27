/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.F0Prism1Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F0Prism2Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F0Prism3Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F0Prism4Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F0Prism5Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F0Prism6Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F0Prism7Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F0Prism8Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F0Prism9Real
public import HlawkaSchatten.BelowExponent.FacetArchive.F0Prism10Real

/-! Archived facet prism certificate data: `F0Root`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

private theorem f0RowsRoot0000 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 1 2) 0 2) 1 2) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 1 2) 0 2) 1 2) = f0Archived1Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f0Archived1Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f0Archived1_rows

private theorem f0RowsRoot0001 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 1 2) 0 2) 2 1) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 1 2) 0 2) 2 1) = f0Archived2Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f0Archived2Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f0Archived2_rows

private theorem f0RowsRoot000 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 1 2) 0 2) := by
  exact facetArchiveTriangle_of_split (i := 1) (j := 2) (by decide) f0RowsRoot0000 f0RowsRoot0001

private theorem f0RowsRoot001 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 1 2) 2 0) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 1 2) 2 0) = f0Archived3Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f0Archived3Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f0Archived3_rows

private theorem f0RowsRoot00 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 1 2) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 2) (by decide) f0RowsRoot000 f0RowsRoot001

private theorem f0RowsRoot0100 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 2 1) 0 1) 1 2) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 2 1) 0 1) 1 2) = f0Archived4Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f0Archived4Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f0Archived4_rows

private theorem f0RowsRoot010100 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 2 1) 0 1) 2 1) 0 1) 1 2) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 2 1) 0 1) 2 1) 0 1) 1 2) = f0Archived5Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f0Archived5Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f0Archived5_rows

private theorem f0RowsRoot010101 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 2 1) 0 1) 2 1) 0 1) 2 1) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 2 1) 0 1) 2 1) 0 1) 2 1) = f0Archived6Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f0Archived6Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f0Archived6_rows

private theorem f0RowsRoot01010 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 2 1) 0 1) 2 1) 0 1) := by
  exact facetArchiveTriangle_of_split (i := 1) (j := 2) (by decide) f0RowsRoot010100 f0RowsRoot010101

private theorem f0RowsRoot01011 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 2 1) 0 1) 2 1) 1 0) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 2 1) 0 1) 2 1) 1 0) = f0Archived7Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f0Archived7Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f0Archived7_rows

private theorem f0RowsRoot0101 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 2 1) 0 1) 2 1) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 1) (by decide) f0RowsRoot01010 f0RowsRoot01011

private theorem f0RowsRoot010 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 2 1) 0 1) := by
  exact facetArchiveTriangle_of_split (i := 1) (j := 2) (by decide) f0RowsRoot0100 f0RowsRoot0101

private theorem f0RowsRoot011 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 2 1) 1 0) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 2 1) 1 0) = f0Archived8Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f0Archived8Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f0Archived8_rows

private theorem f0RowsRoot01 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 0 1) 2 1) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 1) (by decide) f0RowsRoot010 f0RowsRoot011

private theorem f0RowsRoot0 : FacetArchiveTriangle criticalQ (g2SplitTriangle (facetArchiveRoot 0) 0 1) := by
  exact facetArchiveTriangle_of_split (i := 1) (j := 2) (by decide) f0RowsRoot00 f0RowsRoot01

private theorem f0RowsRoot10 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 1 0) 1 2) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 1 0) 1 2) = f0Archived9Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f0Archived9Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f0Archived9_rows

private theorem f0RowsRoot11 : FacetArchiveTriangle criticalQ (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 1 0) 2 1) := by
  have heq : (g2SplitTriangle (g2SplitTriangle (facetArchiveRoot 0) 1 0) 2 1) = f0Archived10Base := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [f0Archived10Base, facetArchiveRoot,
      g2SplitTriangle, Function.update, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [heq]
  exact @f0Archived10_rows

private theorem f0RowsRoot1 : FacetArchiveTriangle criticalQ (g2SplitTriangle (facetArchiveRoot 0) 1 0) := by
  exact facetArchiveTriangle_of_split (i := 1) (j := 2) (by decide) f0RowsRoot10 f0RowsRoot11

theorem f0RowsRoot : FacetArchiveTriangle criticalQ (facetArchiveRoot 0) := by
  exact facetArchiveTriangle_of_split (i := 0) (j := 1) (by decide) f0RowsRoot0 f0RowsRoot1

end HlawkaSchatten.BelowExponent.FacetNumeric
