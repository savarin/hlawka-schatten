/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.CentreLeaves
public import HlawkaSchatten.BelowExponent.Tangent.Tree
public import Mathlib.Analysis.Convex.Combination

/-! Barycentric coordinates of the ordered, depth-truncated simplex in E2's root cell. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Tangent

theorem fine_exponent_bracket :
    (TC.R002_hdr.prof.n1 : ℝ) / TC.R002_hdr.prof.k1 < criticalQ ∧
    criticalQ < (TC.R002_hdr.prof.n2 : ℝ) / TC.R002_hdr.prof.k2 :=
  exponent_bracket_of_tabOK (P := TC.R002_hdr.prof) TC.fine_tab_ok TC.R002_exponent_denominators_pos

private def rootVertices : Fin 4 → TC.V4 :=
  ![⟨3000,3000,3000,3000⟩, ⟨11928,24,24,24⟩, ⟨5976,5976,24,24⟩, ⟨3992,3992,3992,24⟩]

private theorem root_vertex_mem (j : Fin 4) :
    vertex 12000 (rootVertices j) ∈ cellSet (TC.root TC.R002_hdr) := by
  apply subset_convexHull ℝ _
  refine ⟨rootVertices j, ?_, rfl⟩
  fin_cases j <;> simp [TC.cellVerts, TC.root, TC.R002_hdr, TC.vtx, rootVertices]

/-- The actual E2 root includes the interface at minimum coordinate `1/500`. -/
theorem mem_fine_root {t : Profile} (ht : OrderedInterior t) (hd : 1 / 500 ≤ t 3) :
    t ∈ cellSet (TC.root TC.R002_hdr) := by
  let w : Fin 4 → ℝ := ![(500 * t 3 - 1) / 124, 125 * (t 0 - t 1) / 124,
    250 * (t 1 - t 2) / 124, 375 * (t 2 - t 3) / 124]
  let z : Fin 4 → Profile := fun j => vertex 12000 (rootVertices j)
  have hpos : ∀ j ∈ Finset.univ, 0 ≤ w j := by
    intro j _
    fin_cases j <;> simp [w] <;> linarith only [hd, ht.first_ge, ht.second_ge, ht.third_ge]
  have hsum : ∑ j, w j = 1 := by
    simp [Fin.sum_univ_four, w]
    linarith only [ht.sum_four]
  have hrepr : ∑ j, w j • z j = t := by
    funext i
    fin_cases i <;>
      norm_num [Fin.sum_univ_four, w, z, vertex, rootVertices, Pi.smul_apply, smul_eq_mul] <;>
      linarith only [ht.sum_four]
  rw [← hrepr]
  exact (convex_convexHull ℝ _).sum_mem hpos hsum (fun j _ => root_vertex_mem j)

end HlawkaSchatten.BelowExponent.Tangent
