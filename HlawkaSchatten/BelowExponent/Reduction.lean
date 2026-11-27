/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Defs
public import HlawkaSchatten.BelowExponent.Intersection
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Tactic.FinCases

/-! Sum the scalar Route T certificate over a finite set of coordinates to obtain
a unit-ball index for the corresponding four row vectors. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open scoped BigOperators ENNReal

section Coordinates

variable {ι : Type*} [Fintype ι]

/-- The sum of the q-th powers of the absolute coordinates of a vector. -/
noncomputable def coordinatePower (q : ℝ) (v : ι → ℝ) : ℝ :=
  ∑ i, |v i| ^ q

/-- Apply a single weighted row certificate to each coordinate of three vectors. -/
theorem weightedRow_coordinate_sum {q : ℝ} {t π : Profile} {γ : Row}
    (hrow : ∀ x, WeightedRow q t π γ x) (u : Fin 3 → ι → ℝ) :
    (∑ s, π s * coordinatePower q (fun i => rowEval t s (fun j => u j i))) ≤
      ∑ j, γ j * coordinatePower q (u j) := by
  calc
    _ = ∑ i, ∑ s, π s * |rowEval t s (fun j => u j i)| ^ q := by
      simp only [coordinatePower, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ i, ∑ j, γ j * |u j i| ^ q :=
      Finset.sum_le_sum (fun i _ => hrow (fun j => u j i))
    _ = _ := by
      simp only [coordinatePower, Finset.mul_sum]
      rw [Finset.sum_comm]

/-- A simplex-weighted average bounded above by c has an entry at most c. -/
theorem IsSimplex.exists_le_of_weighted_sum_le {π values : Profile} {c : ℝ}
    (hπ : IsSimplex π) (havg : (∑ s, π s * values s) ≤ c) :
    ∃ s, values s ≤ c := by
  by_contra! hall
  obtain ⟨s, hs⟩ : ∃ s, 0 < π s := by
    by_contra! hnonpos
    have hsum : (∑ i, π i) ≤ 0 := Finset.sum_nonpos (fun i _ => hnonpos i)
    rw [hπ.2] at hsum
    exact (not_le_of_gt zero_lt_one) hsum
  have hlt : (∑ i, π i * c) < ∑ i, π i * values i :=
    Finset.sum_lt_sum
      (fun i _ => mul_le_mul_of_nonneg_left (hall i).le (hπ.1 i))
      ⟨s, Finset.mem_univ s, mul_lt_mul_of_pos_left (hall s) hs⟩
  rw [← Finset.sum_mul, hπ.2, one_mul] at hlt
  exact (not_lt_of_ge havg) hlt

/-- At a certified profile, one of the four row vectors has coordinate power at
most one whenever the three input vectors have coordinate power at most one. -/
theorem RowAt.exists_unit_row {q : ℝ} {t : Profile}
    (ht : RowAt q t) (u : Fin 3 → ι → ℝ) (hu : ∀ j, coordinatePower q (u j) ≤ 1) :
    ∃ s, coordinatePower q (fun i => rowEval t s (fun j => u j i)) ≤ 1 := by
  obtain ⟨π, hπ, γ, hγ, hγsum, hrow⟩ := ht
  apply hπ.exists_le_of_weighted_sum_le
  calc
    _ ≤ ∑ j, γ j * coordinatePower q (u j) := weightedRow_coordinate_sum hrow u
    _ ≤ ∑ j, γ j := by
      simpa only [mul_one] using
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hu j) (hγ j))
    _ ≤ 1 := hγsum

/-- The coordinate-power criterion is equivalent to membership in the closed
unit ball for a finite positive exponent. -/
theorem norm_toLp_le_one_iff_coordinatePower {p : ℝ≥0∞} (hp : 0 < p.toReal) (v : ι → ℝ) :
    ‖WithLp.toLp p v‖ ≤ 1 ↔ coordinatePower p.toReal v ≤ 1 := by
  rw [PiLp.norm_eq_sum hp]
  simp only [Real.norm_eq_abs]
  change coordinatePower p.toReal v ^ (1 / p.toReal) ≤ 1 ↔ coordinatePower p.toReal v ≤ 1
  have hv : 0 ≤ coordinatePower p.toReal v :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg (v i)) _)
  simpa only [Real.one_rpow] using
    (Real.rpow_le_rpow_iff hv zero_le_one (one_div_pos.mpr hp))

/-- The four row vectors cover the profile in the unit-ball test of Theorem T. -/
theorem RowAt.exists_unit_ball_index {p : ℝ≥0∞} {t : Profile}
    (hp : 0 < p.toReal) (ht : RowAt p.toReal t)
    (u : Fin 3 → PiLp p (fun _ : ι => ℝ)) (hu : ∀ j, ‖u j‖ ≤ 1) :
    ∃ s, ‖WithLp.toLp p (fun i => rowEval t s (fun j => u j i))‖ ≤ 1 := by
  have hinput : ∀ j, coordinatePower p.toReal (fun i => u j i) ≤ 1 := fun j =>
    (norm_toLp_le_one_iff_coordinatePower hp (fun i => u j i)).mp (hu j)
  obtain ⟨s, hs⟩ := ht.exists_unit_row (fun j i => u j i) hinput
  exact ⟨s, (norm_toLp_le_one_iff_coordinatePower hp _).mpr hs⟩

end Coordinates

section Geometry

noncomputable def centerCoord (s : Fin 4) (x : Row) : ℝ :=
  (∑ j, sign j s * x j) / 2

private theorem rowEval_eq_centerCoord_add {t : Profile} (ht : ∑ r, t r = 1) (s : Fin 4) (x : Row) :
    rowEval t s x = centerCoord s x + ∑ r, t r * centerCoord r x := by
  have hcenter : centerCoord s x = ∑ r, t r * centerCoord s x := by
    rw [← Finset.sum_mul, ht, one_mul]
  calc
    rowEval t s x = (∑ r, t r * centerCoord s x) + ∑ r, t r * centerCoord r x := by
      fin_cases s <;> simp (config := { decide := true }) [rowEval, centerCoord, sign, partner,
        Fin.sum_univ_three, Fin.sum_univ_four] <;> ring
    _ = _ := by rw [← hcenter]

variable {ι : Type*}

/-- The signed centers in Theorem T. -/
noncomputable def routeTCenter {p : ℝ≥0∞} (u : Fin 3 → PiLp p (fun _ : ι => ℝ))
    (s : Fin 4) : PiLp p (fun _ : ι => ℝ) :=
  WithLp.toLp p (fun i => centerCoord s (fun j => u j i))

/-- The affine point tested against each signed center at a simplex profile. -/
noncomputable def routeTPoint {p : ℝ≥0∞} (u : Fin 3 → PiLp p (fun _ : ι => ℝ)) :
    Profile →ₗ[ℝ] PiLp p (fun _ : ι => ℝ) where
  toFun t := -∑ r, t r • routeTCenter u r
  map_add' t v := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib, add_comm]
  map_smul' a t := by simp [Pi.smul_apply, smul_neg, Finset.smul_sum, smul_smul]

theorem continuous_routeTPoint {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fintype ι]
    (u : Fin 3 → PiLp p (fun _ : ι => ℝ)) :
    Continuous (routeTPoint u : Profile → PiLp p (fun _ : ι => ℝ)) := by
  change Continuous (fun t : Profile => -∑ r, t r • routeTCenter u r)
  exact (continuous_finsetSum _ fun r _ => (continuous_apply r).smul continuous_const).neg

theorem routeTCenter_sub_point_eq_rowEval {p : ℝ≥0∞} (u : Fin 3 → PiLp p (fun _ : ι => ℝ))
    {t : Profile} (ht : IsSimplex t) (s : Fin 4) :
    routeTCenter u s - routeTPoint u t =
      WithLp.toLp p (fun i => rowEval t s (fun j => u j i)) := by
  ext i
  simp [routeTPoint, routeTCenter, rowEval_eq_centerCoord_add ht.2]

/-- Every certified simplex profile belongs to at least one of the four closed
unit-ball preimages in Theorem T. -/
theorem RowAt.exists_center_sub_point_norm_le_one [Fintype ι] {p : ℝ≥0∞} {t : Profile}
    (hp : 0 < p.toReal) (ht : IsSimplex t) (hrow : RowAt p.toReal t)
    (u : Fin 3 → PiLp p (fun _ : ι => ℝ)) (hu : ∀ j, ‖u j‖ ≤ 1) :
    ∃ s, ‖routeTCenter u s - routeTPoint u t‖ ≤ 1 := by
  obtain ⟨s, hs⟩ := hrow.exists_unit_ball_index hp u hu
  exact ⟨s, routeTCenter_sub_point_eq_rowEval u ht s ▸ hs⟩

private theorem exists_partner {s r : Fin 4} (hrs : r ≠ s) :
    ∃ j, partner j s = r := by
  fin_cases s <;> fin_cases r <;> first | exact (hrs rfl).elim | decide

theorem routeTCenter_add_partner {p : ℝ≥0∞} (u : Fin 3 → PiLp p (fun _ : ι => ℝ))
    (s : Fin 4) (j : Fin 3) :
    routeTCenter u s + routeTCenter u (partner j s) = sign j s • u j := by
  ext i
  simp only [PiLp.add_apply, routeTCenter, PiLp.smul_apply, smul_eq_mul]
  fin_cases s <;> fin_cases j <;> simp (config := { decide := true })
    [centerCoord, sign, partner, Fin.sum_univ_three] <;> ring

theorem routeTPoint_at_vertex {p : ℝ≥0∞} (u : Fin 3 → PiLp p (fun _ : ι => ℝ)) (r : Fin 4) :
    routeTPoint u (Pi.single r 1) = -routeTCenter u r := by
  classical
  change -(∑ i, (Pi.single r (1 : ℝ) : Profile) i • routeTCenter u i) = -routeTCenter u r
  congr 1
  rw [Finset.sum_eq_single r]
  · simp
  · intro i _ hir
    simp [Pi.single_eq_of_ne hir]
  · simp

/-- The vertex indexed by r lies in the ball for any distinct index s. -/
theorem routeTCenter_sub_vertex_norm_le_one {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fintype ι]
    (u : Fin 3 → PiLp p (fun _ : ι => ℝ)) (hu : ∀ j, ‖u j‖ ≤ 1)
    {s r : Fin 4} (hrs : r ≠ s) :
    ‖routeTCenter u s - routeTPoint u (Pi.single r 1)‖ ≤ 1 := by
  obtain ⟨j, rfl⟩ := exists_partner hrs
  rw [routeTPoint_at_vertex, sub_neg_eq_add, routeTCenter_add_partner, norm_smul]
  simpa [sign, apply_ite] using hu j

/-- Profiles whose image under the Route T map is in the closed unit ball at
the given signed center. -/
noncomputable def routeTUnitSet {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fintype ι]
    (u : Fin 3 → PiLp p (fun _ : ι => ℝ)) (s : Fin 4) : Set Profile :=
  routeTPoint u ⁻¹' Metric.closedBall (routeTCenter u s) 1

theorem mem_routeTUnitSet {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fintype ι]
    {u : Fin 3 → PiLp p (fun _ : ι => ℝ)} {s : Fin 4} {t : Profile} :
    t ∈ routeTUnitSet u s ↔ ‖routeTCenter u s - routeTPoint u t‖ ≤ 1 := by
  simp only [routeTUnitSet, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  rw [norm_sub_rev]

theorem isClosed_routeTUnitSet {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fintype ι]
    (u : Fin 3 → PiLp p (fun _ : ι => ℝ)) (s : Fin 4) :
    IsClosed (routeTUnitSet u s) :=
  Metric.isClosed_closedBall.preimage (continuous_routeTPoint u)

theorem convex_routeTUnitSet {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fintype ι]
    (u : Fin 3 → PiLp p (fun _ : ι => ℝ)) (s : Fin 4) :
    Convex ℝ (routeTUnitSet u s) :=
  (convex_closedBall (routeTCenter u s) 1).linear_preimage (routeTPoint u)


theorem RowAt.exists_mem_routeTUnitSet {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fintype ι]
    {t : Profile} (hp : 0 < p.toReal) (ht : IsSimplex t) (hrow : RowAt p.toReal t)
    (u : Fin 3 → PiLp p (fun _ : ι => ℝ)) (hu : ∀ j, ‖u j‖ ≤ 1) :
    ∃ s, t ∈ routeTUnitSet u s := by
  obtain ⟨s, hs⟩ := hrow.exists_center_sub_point_norm_le_one hp ht u hu
  exact ⟨s, mem_routeTUnitSet.mpr hs⟩

theorem vertex_mem_routeTUnitSet {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fintype ι]
    (u : Fin 3 → PiLp p (fun _ : ι => ℝ)) (hu : ∀ j, ‖u j‖ ≤ 1) {s r : Fin 4}
    (hrs : r ≠ s) : Pi.single r 1 ∈ routeTUnitSet u s :=
  mem_routeTUnitSet.mpr (routeTCenter_sub_vertex_norm_le_one u hu hrs)

/-- The simplex profiles form a convex set. -/
private theorem convex_isSimplex : Convex ℝ {t : Profile | IsSimplex t} := by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
  · simp_rw [Pi.add_apply, Pi.smul_apply]
    rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one]

/-- The simplex profiles form a compact set: a closed subset of the unit cube. -/
private theorem isCompact_isSimplex : IsCompact {t : Profile | IsSimplex t} := by
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : Profile)) (b := 1)) ?_ ?_
  · have hset : {t : Profile | IsSimplex t} =
        (⋂ s, {t : Profile | 0 ≤ t s}) ∩ {t : Profile | ∑ s, t s = 1} := by
      ext t
      simp [IsSimplex]
    rw [hset]
    apply IsClosed.inter
    · exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
    · exact isClosed_eq (by fun_prop) continuous_const
  · intro t ht
    refine ⟨fun s => ht.1 s, fun s => ?_⟩
    calc t s ≤ ∑ r, t r := Finset.single_le_sum (fun r _ => ht.1 r) (Finset.mem_univ s)
      _ = 1 := ht.2

/-- Each vertex of the simplex is a simplex profile. -/
private theorem isSimplex_single (r : Fin 4) : IsSimplex (Pi.single r 1) :=
  ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩

/-- If the row certificate holds at every simplex profile, the four geometric
unit balls have a common point given by a simplex profile. -/
theorem exists_common_routeTPoint {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fintype ι]
    (hp : 0 < p.toReal) (hrows : ∀ t : Profile, IsSimplex t → RowAt p.toReal t)
    (u : Fin 3 → PiLp p (fun _ : ι => ℝ)) (hu : ∀ j, ‖u j‖ ≤ 1) :
    ∃ t : Profile, IsSimplex t ∧ ∀ s, ‖routeTCenter u s - routeTPoint u t‖ ≤ 1 := by
  let D : Set Profile := {t | IsSimplex t}
  let C (s : Fin 4) : Set Profile := D ∩ routeTUnitSet u s
  have hDconvex : Convex ℝ D := convex_isSimplex
  have hDcompact : IsCompact D := isCompact_isSimplex
  have hcover : (⋃ s, C s) = D := by
    ext t
    constructor
    · intro ht
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ht
      exact hs.1
    · intro ht
      obtain ⟨s, hs⟩ := (hrows t ht).exists_mem_routeTUnitSet hp ht u hu
      exact Set.mem_iUnion.mpr ⟨s, ht, hs⟩
  obtain ⟨t, ht, hcommon⟩ := four_set_intersection C D (fun r => Pi.single r 1)
    (fun s => hDconvex.inter (convex_routeTUnitSet u s))
    (fun s => hDcompact.inter_right (isClosed_routeTUnitSet u s))
    hcover hDconvex isSimplex_single
    (fun r s hsr => ⟨isSimplex_single r, vertex_mem_routeTUnitSet u hu hsr.symm⟩)
  exact ⟨t, ht, fun s => mem_routeTUnitSet.mp (hcommon s).2⟩

end Geometry

end HlawkaSchatten.BelowExponent
