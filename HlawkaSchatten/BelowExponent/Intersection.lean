/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Tactic.Linarith

/-!
# Klee's intersection lemma for compact convex sets

Induction on the family size uses a separating functional and a slice between the two
separated sets. See V. L. Klee, Jr., *On Certain Intersection Properties of Convex Sets*,
Canad. J. Math. 3 (1951), (2.1), p. 272.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem exists_on_slice (f : StrongDual ℝ E) {u : ℝ} {x y : E}
    (hx : f x < u) (hy : u < f y) :
    ∃ z ∈ segment ℝ x y, f z = u := by
  let b := (u - f x) / (f y - f x)
  have hd : 0 < f y - f x := by linarith
  have hb₀ : 0 ≤ b := div_nonneg (sub_nonneg.mpr hx.le) hd.le
  have hb₁ : b ≤ 1 := (div_le_one hd).2 (by linarith)
  have hb : b * (f y - f x) = u - f x := div_mul_cancel₀ _ hd.ne'
  refine ⟨(1-b) • x + b • y, ⟨1-b, b, by linarith, hb₀, by ring, rfl⟩, ?_⟩
  simp only [map_add, map_smul, smul_eq_mul]
  linarith only [hb]

/-- If the union is convex and each omitted set leaves a common point inside the union,
then the entire family has a common point. The union clause also covers the one-set base case. -/
theorem klee_intersection (n : ℕ) (C : Fin (n+1) → Set E)
    (hc : ∀ i, Convex ℝ (C i)) (hk : ∀ i, IsCompact (C i))
    (hU : Convex ℝ (⋃ i, C i))
    (hw : ∀ k, ∃ x ∈ ⋃ i, C i, ∀ j, j ≠ k → x ∈ C j) :
    ∃ x, ∀ i, x ∈ C i := by
  classical
  induction n with
  | zero =>
    obtain ⟨x, hx, -⟩ := hw 0
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨x, fun j => Subsingleton.elim (α := Fin 1) i j ▸ hi⟩
  | succ n ih =>
    by_contra hnone
    let K := ⋂ i : Fin (n+1), C i.succ
    have hKc : Convex ℝ K := convex_iInter fun i => hc i.succ
    have hKk : IsCompact K := (hk (Fin.succ (0 : Fin (n+1)))).of_isClosed_subset
      (isClosed_iInter fun i => (hk i.succ).isClosed) (iInter_subset _ 0)
    have hdisj : Disjoint K (C 0) := by
      apply Set.disjoint_left.2
      intro x hx hx₀
      exact hnone ⟨x, Fin.cases hx₀ (Set.mem_iInter.mp hx)⟩
    obtain ⟨f, u, v, hleft, huv, hright⟩ :=
      geometric_hahn_banach_compact_closed hKc hKk (hc 0) (hk 0).isClosed hdisj
    let H := {x : E | f x = u}
    have hHclosed : IsClosed H := isClosed_eq f.continuous continuous_const
    have hHconvex : Convex ℝ H := convex_hyperplane f.toLinearMap.isLinear u
    let D (i : Fin (n+1)) := C i.succ ∩ H
    have hslice : (⋃ i, D i) = (⋃ i, C i) ∩ H := by
      ext z
      constructor
      · rintro hz
        obtain ⟨i, hi⟩ := mem_iUnion.mp hz
        exact ⟨mem_iUnion.mpr ⟨i.succ, hi.1⟩, hi.2⟩
      · rintro ⟨hz, hzH⟩
        obtain ⟨i, hi⟩ := mem_iUnion.mp hz
        cases i using Fin.cases with
        | zero => exact False.elim ((ne_of_gt (huv.trans (hright z hi))) hzH)
        | succ j => exact mem_iUnion.mpr ⟨j, hi, hzH⟩
    obtain ⟨x, hxU, hxRest⟩ := hw 0
    have hxK : x ∈ K := mem_iInter.mpr fun j => hxRest _ (Fin.succ_ne_zero j)
    have hwD : ∀ k : Fin (n+1), ∃ z ∈ ⋃ j, D j, ∀ j, j ≠ k → z ∈ D j := by
      intro k
      obtain ⟨y, hyU, hyRest⟩ := hw k.succ
      have hy₀ := hyRest 0 (Fin.succ_ne_zero k).symm
      obtain ⟨z, hseg, hzu⟩ := exists_on_slice f (hleft _ hxK) (huv.trans (hright _ hy₀))
      refine ⟨z, hslice.symm ▸ ⟨hU.segment_subset hxU hyU hseg, hzu⟩, ?_⟩
      intro j hj
      exact ⟨(hc j.succ).segment_subset (mem_iInter.mp hxK j)
        (hyRest _ (fun e => hj (Fin.succ_injective _ e))) hseg, hzu⟩
    have hDU : Convex ℝ (⋃ i, D i) := hslice.symm ▸ hU.inter hHconvex
    obtain ⟨z, hz⟩ := ih D (fun i => (hc i.succ).inter hHconvex)
      (fun i => (hk i.succ).inter_right hHclosed) hDU hwD
    have hzK : z ∈ K := mem_iInter.mpr fun j => (hz j).1
    exact (ne_of_lt (hleft z hzK)) (hz 0).2

/-- The four-set form needed by Route T. Vertex k supplies the witness for omitting set k. -/
theorem four_set_intersection (C : Fin 4 → Set E) (D : Set E) (vertex : Fin 4 → E)
    (hc : ∀ i, Convex ℝ (C i)) (hk : ∀ i, IsCompact (C i))
    (hU : (⋃ i, C i) = D) (hD : Convex ℝ D) (hv : ∀ i, vertex i ∈ D)
    (hface : ∀ k j, j ≠ k → vertex k ∈ C j) :
    ∃ x ∈ D, ∀ i, x ∈ C i := by
  obtain ⟨x, hx⟩ := klee_intersection 3 C hc hk (hU.symm ▸ hD)
    (fun k => ⟨vertex k, hU.symm ▸ hv k, hface k⟩)
  exact ⟨x, hU ▸ mem_iUnion.mpr ⟨0, hx 0⟩, hx⟩

end HlawkaSchatten.BelowExponent
