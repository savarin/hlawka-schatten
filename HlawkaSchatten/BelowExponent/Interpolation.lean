/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Defs
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Convex interpolation for the Route T row inequality and its specialization to the
split of the last two profile coordinates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

/-- Linear interpolation of profiles, with the second endpoint at `u = 1`. -/
def profileLerp (u : ℝ) (t₀ t₁ : Profile) : Profile :=
  fun s => (1 - u) * t₀ s + u * t₁ s

/-- Linear interpolation of the three row weights. -/
def rowLerp (u : ℝ) (γ₀ γ₁ : Row) : Row :=
  fun j => (1 - u) * γ₀ j + u * γ₁ j

theorem rowEval_profileLerp (u : ℝ) (t₀ t₁ : Profile) (s : Fin 4) (x : Row) :
    rowEval (profileLerp u t₀ t₁) s x =
      (1 - u) * rowEval t₀ s x + u * rowEval t₁ s x := by
  unfold rowEval profileLerp
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem abs_rpow_lerp_le {q u : ℝ} (hq : 1 ≤ q) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1)
    (a b : ℝ) : |(1 - u) * a + u * b| ^ q ≤ (1 - u) * |a| ^ q + u * |b| ^ q := by
  have hu : 0 ≤ 1 - u := sub_nonneg.mpr hu₁
  have hAbs : |(1 - u) * a + u * b| ≤ (1 - u) * |a| + u * |b| := by
    simpa only [abs_mul, abs_of_nonneg hu, abs_of_nonneg hu₀] using
      (abs_add_le ((1 - u) * a) (u * b))
  refine (Real.rpow_le_rpow (abs_nonneg _) hAbs (zero_le_one.trans hq)).trans ?_
  simpa only [smul_eq_mul] using (convexOn_rpow hq).2
    (Set.mem_Ici.mpr (abs_nonneg a)) (Set.mem_Ici.mpr (abs_nonneg b)) hu hu₀ (sub_add_cancel 1 u)

theorem abs_rowEval_rpow_profileLerp_le {q u : ℝ} (hq : 1 ≤ q) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1)
    (t₀ t₁ : Profile) (s : Fin 4) (x : Row) :
    |rowEval (profileLerp u t₀ t₁) s x| ^ q ≤
      (1 - u) * |rowEval t₀ s x| ^ q + u * |rowEval t₁ s x| ^ q := by
  rw [rowEval_profileLerp]
  exact abs_rpow_lerp_le hq hu₀ hu₁ _ _

theorem convexOn_abs_rowEval_rpow {q : ℝ} (hq : 1 ≤ q) (s : Fin 4) (x : Row) :
    ConvexOn ℝ Set.univ fun t : Profile => |rowEval t s x| ^ q := by
  refine ⟨convex_univ, ?_⟩
  intro t₀ _ t₁ _ a b ha hb hab
  have ha' : a = 1 - b := by linarith
  have hb' : b ≤ 1 := by linarith
  have ht : a • t₀ + b • t₁ = profileLerp b t₀ t₁ := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, profileLerp, ha']
  rw [ht]
  simpa only [smul_eq_mul, ha'] using abs_rowEval_rpow_profileLerp_le hq hb hb' t₀ t₁ s x

/-- Fixed nonnegative profile weights allow interpolation of the profile and row weights. -/
theorem weightedRow_profileLerp {q u : ℝ} {t₀ t₁ π : Profile} {γ₀ γ₁ x : Row}
    (hq : 1 ≤ q) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (hπ : ∀ s, 0 ≤ π s)
    (h₀ : WeightedRow q t₀ π γ₀ x) (h₁ : WeightedRow q t₁ π γ₁ x) :
    WeightedRow q (profileLerp u t₀ t₁) π (rowLerp u γ₀ γ₁) x := by
  unfold WeightedRow at *
  have hu : 0 ≤ 1 - u := sub_nonneg.mpr hu₁
  calc
    _ ≤ ∑ s : Fin 4, ((1 - u) * (π s * |rowEval t₀ s x| ^ q) +
        u * (π s * |rowEval t₁ s x| ^ q)) := by
      refine Finset.sum_le_sum fun s _ => ?_
      calc
        _ ≤ π s * ((1 - u) * |rowEval t₀ s x| ^ q + u * |rowEval t₁ s x| ^ q) :=
          mul_le_mul_of_nonneg_left (abs_rowEval_rpow_profileLerp_le hq hu₀ hu₁ t₀ t₁ s x) (hπ s)
        _ = _ := by ring
    _ = (1 - u) * (∑ s, π s * |rowEval t₀ s x| ^ q) +
        u * (∑ s, π s * |rowEval t₁ s x| ^ q) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (1 - u) * (∑ j, γ₀ j * |x j| ^ q) + u * (∑ j, γ₁ j * |x j| ^ q) :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ hu) (mul_le_mul_of_nonneg_left h₁ hu₀)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by unfold rowLerp; ring

theorem weightedRow_profileLerp_fixed {q u : ℝ} {t₀ t₁ π : Profile} {γ x : Row}
    (hq : 1 ≤ q) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (hπ : ∀ s, 0 ≤ π s)
    (h₀ : WeightedRow q t₀ π γ x) (h₁ : WeightedRow q t₁ π γ x) :
    WeightedRow q (profileLerp u t₀ t₁) π γ x := by
  have hγ : rowLerp u γ γ = γ := by
    funext j
    unfold rowLerp
    ring
  simpa only [hγ] using weightedRow_profileLerp hq hu₀ hu₁ hπ h₀ h₁

/-- A single choice of profile weights can certify a whole polytope from its vertices. -/
theorem weightedRow_barycenter {ι : Type*} {q : ℝ} {vertices : Finset ι}
    {w : ι → ℝ} {t : ι → Profile} {π : Profile} {γ : ι → Row} {x : Row}
    (hq : 1 ≤ q) (hw : ∀ i ∈ vertices, 0 ≤ w i) (hSum : ∑ i ∈ vertices, w i = 1)
    (hπ : ∀ s, 0 ≤ π s) (hRows : ∀ i ∈ vertices, WeightedRow q (t i) π (γ i) x) :
    WeightedRow q (∑ i ∈ vertices, w i • t i) π (∑ i ∈ vertices, w i • γ i) x := by
  unfold WeightedRow at *
  calc
    _ ≤ ∑ s : Fin 4, π s * (∑ i ∈ vertices, w i * |rowEval (t i) s x| ^ q) := by
      refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (hπ s)
      simpa only [smul_eq_mul] using (convexOn_abs_rowEval_rpow hq s x).map_sum_le
        (p := t) hw hSum (fun i _ => Set.mem_univ (t i))
    _ = ∑ i ∈ vertices, w i * (∑ s, π s * |rowEval (t i) s x| ^ q) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => by ring
    _ ≤ ∑ i ∈ vertices, w i * (∑ j, γ i j * |x j| ^ q) :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hRows i hi) (hw i hi)
    _ = _ := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem rowAt_barycenter {ι : Type*} {q : ℝ} {vertices : Finset ι}
    {w : ι → ℝ} {t : ι → Profile} {π : Profile} {γ : ι → Row}
    (hq : 1 ≤ q) (hw : ∀ i ∈ vertices, 0 ≤ w i) (hSum : ∑ i ∈ vertices, w i = 1)
    (hπ : IsSimplex π) (hγ : ∀ i ∈ vertices, ∀ j, 0 ≤ γ i j)
    (hBudget : ∀ i ∈ vertices, ∑ j, γ i j ≤ 1)
    (hRows : ∀ i ∈ vertices, ∀ x, WeightedRow q (t i) π (γ i) x) :
    RowAt q (∑ i ∈ vertices, w i • t i) := by
  refine ⟨π, hπ, ∑ i ∈ vertices, w i • γ i, ?_, ?_, ?_⟩
  · intro j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hγ i hi j)
  · calc
      _ = ∑ i ∈ vertices, w i * (∑ j, γ i j) := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ ∑ i ∈ vertices, w i := by
        refine Finset.sum_le_sum fun i hi => ?_
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hBudget i hi) (hw i hi)
      _ = 1 := hSum
  · intro x
    exact weightedRow_barycenter hq hw hSum hπ.1 fun i hi => hRows i hi x

private def rowEvalLinear (t : Profile) (s : Fin 4) : Row →ₗ[ℝ] ℝ where
  toFun := rowEval t s
  map_add' := by
    intro x y
    simp only [rowEval, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    change rowEval t s (a • x) = a * rowEval t s x
    unfold rowEval
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem rowEval_smul (t : Profile) (s : Fin 4) (a : ℝ) (x : Row) :
    rowEval t s (a • x) = a * rowEval t s x :=
  (rowEvalLinear t s).map_smul a x

theorem convexOn_abs_rowEval_row_rpow {q : ℝ} (hq : 1 ≤ q) (t : Profile) (s : Fin 4) :
    ConvexOn ℝ Set.univ fun x : Row => |rowEval t s x| ^ q := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v hu hv hSum
  have hu' : u = 1 - v := by linarith
  have hv' : v ≤ 1 := by linarith
  have hAdd : rowEval t s (u • x + v • y) = rowEval t s (u • x) + rowEval t s (v • y) :=
    (rowEvalLinear t s).map_add _ _
  change |rowEval t s (u • x + v • y)| ^ q ≤
    u * |rowEval t s x| ^ q + v * |rowEval t s y| ^ q
  rw [hAdd, rowEval_smul, rowEval_smul, hu']
  exact abs_rpow_lerp_le hq hv hv' (rowEval t s x) (rowEval t s y)

/-- A weighted average of affine lower input bounds can certify an interpolated row. -/
theorem weightedRow_rowBarycenter {ι : Type*} {q : ℝ} {vertices : Finset ι}
    {w : ι → ℝ} {t π : Profile} {γ : Row} {x ν : ι → Row}
    (hq : 1 ≤ q) (hw : ∀ i ∈ vertices, 0 ≤ w i) (hSum : ∑ i ∈ vertices, w i = 1)
    (hπ : ∀ s, 0 ≤ π s) (hγ : ∀ j, 0 ≤ γ j)
    (hCorners : ∀ i ∈ vertices, ∑ s, π s * |rowEval t s (x i)| ^ q ≤ ∑ j, γ j * ν i j)
    (hLower : ∀ j, (∑ i ∈ vertices, w i * ν i j) ≤ |(∑ i ∈ vertices, w i • x i) j| ^ q) :
    WeightedRow q t π γ (∑ i ∈ vertices, w i • x i) := by
  unfold WeightedRow
  calc
    _ ≤ ∑ s : Fin 4, π s * (∑ i ∈ vertices, w i * |rowEval t s (x i)| ^ q) := by
      refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (hπ s)
      simpa only [smul_eq_mul] using (convexOn_abs_rowEval_row_rpow hq t s).map_sum_le
        (p := x) hw hSum (fun i _ => Set.mem_univ (x i))
    _ = ∑ i ∈ vertices, w i * (∑ s, π s * |rowEval t s (x i)| ^ q) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => by ring
    _ ≤ ∑ i ∈ vertices, w i * (∑ j, γ j * ν i j) :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hCorners i hi) (hw i hi)
    _ = ∑ j, γ j * (∑ i ∈ vertices, w i * ν i j) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hLower j) (hγ j)

theorem weightedRow_smul_iff {q a : ℝ} {t π : Profile} {γ x : Row} (ha : a ≠ 0) :
    WeightedRow q t π γ (a • x) ↔ WeightedRow q t π γ x := by
  have hPower (b : ℝ) : |a * b| ^ q = |a| ^ q * |b| ^ q := by
    rw [abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg b)]
  unfold WeightedRow
  simp only [rowEval_smul, Pi.smul_apply, smul_eq_mul, hPower]
  simp_rw [mul_left_comm _ (|a| ^ q), ← Finset.mul_sum]
  exact mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos (abs_pos.mpr ha) q)

/-- The three bounded row charts with one coordinate set to one cover all nonzero rows. -/
theorem weightedRow_of_normalized_charts {q : ℝ} {t π : Profile} {γ : Row}
    (hq : 0 < q)
    (hChart : ∀ (k : Fin 3) (x : Row),
      x k = 1 → (∀ j, |x j| ≤ 1) → WeightedRow q t π γ x) :
    ∀ x, WeightedRow q t π γ x := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [WeightedRow, rowEval, Real.zero_rpow hq.ne']
  · obtain ⟨k, _, hMax⟩ :=
      Finset.exists_max_image Finset.univ (fun j => |x j|) Finset.univ_nonempty
    have hk : x k ≠ 0 := by
      intro hZero
      apply hx
      funext j
      change x j = 0
      exact abs_eq_zero.mp <|
        le_antisymm (by simpa [hZero] using hMax j (Finset.mem_univ j)) (abs_nonneg (x j))
    apply (weightedRow_smul_iff (a := (x k)⁻¹) (inv_ne_zero hk)).mp
    apply hChart k
    · simp [Pi.smul_apply, smul_eq_mul, hk]
    · intro j
      simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, div_eq_inv_mul] using
        (div_le_one₀ (abs_pos.mpr hk)).mpr (hMax j (Finset.mem_univ j))

/-- The last two coordinates have sum `l` and difference `d`. -/
noncomputable def splitProfile (a b l d : ℝ) : Profile :=
  ![a, b, (l + d) / 2, (l - d) / 2]

/-- With both weights held fixed, the two facet endpoints control every split. -/
theorem weightedRow_split {q a b l d : ℝ} {π : Profile} {γ x : Row}
    (hq : 1 ≤ q) (hd : |d| ≤ l) (hπ : ∀ s, 0 ≤ π s)
    (hLower : WeightedRow q (splitProfile a b l (-l)) π γ x)
    (hUpper : WeightedRow q (splitProfile a b l l) π γ x) :
    WeightedRow q (splitProfile a b l d) π γ x := by
  by_cases hl : l = 0
  · have hd₀ : d = 0 := abs_eq_zero.mp (le_antisymm (hl ▸ hd) (abs_nonneg d))
    simpa only [hl, hd₀] using hUpper
  · have hl₀ : 0 < l := lt_of_le_of_ne ((abs_nonneg d).trans hd) (Ne.symm hl)
    have hden : 0 < 2 * l := mul_pos two_pos hl₀
    have hdl := abs_le.mp hd
    let u := (d + l) / (2 * l)
    have hu₀ : 0 ≤ u := div_nonneg (by linarith [hdl.1]) hden.le
    have hu₁ : u ≤ 1 := (div_le_iff₀ hden).2 (by linarith [hdl.2])
    have ht : splitProfile a b l d =
        profileLerp u (splitProfile a b l (-l)) (splitProfile a b l l) := by
      funext s
      fin_cases s <;> simp [splitProfile, profileLerp, u] <;> field_simp [hl] <;> ring
    rw [ht]
    exact weightedRow_profileLerp_fixed hq hu₀ hu₁ hπ hLower hUpper

private abbrev swapLast : Fin 4 ≃ Fin 4 := Equiv.swap 2 3
private abbrev swapFirst : Fin 3 ≃ Fin 3 := Equiv.swap 0 1

private theorem partner_swapLast (j : Fin 3) (s : Fin 4) :
    swapLast (partner j s) = partner (swapFirst j) (swapLast s) := by
  fin_cases j <;> fin_cases s <;> decide

private theorem sign_swapLast (j : Fin 3) (s : Fin 4) :
    sign j s = sign (swapFirst j) (swapLast s) := by
  have hzero : swapLast 0 = 0 := by decide
  have h₀ : swapLast s = 0 ↔ s = 0 := by
    simpa only [hzero] using
      (swapLast.apply_eq_iff_eq : swapLast s = swapLast 0 ↔ s = 0)
  have hp : swapLast s = partner (swapFirst j) 0 ↔ s = partner j 0 := by
    simpa only [partner_swapLast j 0, hzero] using
      (swapLast.apply_eq_iff_eq : swapLast s = swapLast (partner j 0) ↔ s = partner j 0)
  simp only [sign, h₀, hp]

private theorem rowEval_swapLast (t : Profile) (s : Fin 4) (x : Row) :
    rowEval (t ∘ swapLast) s x = rowEval t (swapLast s) (x ∘ swapFirst.symm) := by
  unfold rowEval
  calc
    _ = ∑ j, sign (swapFirst j) (swapLast s) *
        (t (swapLast s) + t (partner (swapFirst j) (swapLast s))) *
        (x ∘ swapFirst.symm) (swapFirst j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      rw [partner_swapLast j s, sign_swapLast j s]
    _ = _ := swapFirst.sum_comp fun j =>
      sign j (swapLast s) * (t (swapLast s) + t (partner j (swapLast s))) *
        (x ∘ swapFirst.symm) j

private theorem weightedRow_swapLast_iff {q : ℝ} {t π : Profile} {γ x : Row}
    (hπ : π 2 = π 3) (hγ : γ 0 = γ 1) :
    WeightedRow q (t ∘ swapLast) π γ x ↔ WeightedRow q t π γ (x ∘ swapFirst.symm) := by
  unfold WeightedRow
  have hOut : (∑ s, π s * |rowEval (t ∘ swapLast) s x| ^ q) =
      ∑ s, π s * |rowEval t s (x ∘ swapFirst.symm)| ^ q := by
    calc
      _ = ∑ s, π (swapLast s) * |rowEval t (swapLast s) (x ∘ swapFirst.symm)| ^ q := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [rowEval_swapLast, Equiv.apply_swap_eq_self hπ s]
      _ = _ := swapLast.sum_comp fun s => π s * |rowEval t s (x ∘ swapFirst.symm)| ^ q
  have hIn : (∑ j, γ j * |x j| ^ q) = ∑ j, γ j * |(x ∘ swapFirst.symm) j| ^ q := by
    calc
      _ = ∑ j, γ (swapFirst j) * |(x ∘ swapFirst.symm) (swapFirst j)| ^ q := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.apply_swap_eq_self hγ]
      _ = _ := swapFirst.sum_comp fun j => γ j * |(x ∘ swapFirst.symm) j| ^ q
  rw [hOut, hIn]

/-- The balanced G1 and G3 weights identify the two facet inequalities by reflection. -/
theorem weightedRow_split_of_facet {q a b l d : ℝ} {π : Profile} {γ : Row}
    (hq : 1 ≤ q) (hd : |d| ≤ l) (hπ : ∀ s, 0 ≤ π s)
    (hπeq : π 2 = π 3) (hγeq : γ 0 = γ 1)
    (hFacet : ∀ x, WeightedRow q (splitProfile a b l l) π γ x) :
    ∀ x, WeightedRow q (splitProfile a b l d) π γ x := by
  have hFlip : splitProfile a b l (-l) = splitProfile a b l l ∘ swapLast := by
    funext s
    fin_cases s <;> simp [splitProfile, swapLast, Equiv.swap_apply_def]
  intro x
  refine weightedRow_split hq hd hπ ?_ (hFacet x)
  rw [hFlip, weightedRow_swapLast_iff hπeq hγeq]
  exact hFacet _

/-- Apply the one-facet reduction directly to a profile with nonnegative last coordinates. -/
theorem weightedRow_of_lastFacet {q : ℝ} {t π : Profile} {γ : Row}
    (hq : 1 ≤ q) (ht₂ : 0 ≤ t 2) (ht₃ : 0 ≤ t 3) (hπ : ∀ s, 0 ≤ π s)
    (hπeq : π 2 = π 3) (hγeq : γ 0 = γ 1)
    (hFacet : ∀ x, WeightedRow q ![t 0, t 1, t 2 + t 3, 0] π γ x) :
    ∀ x, WeightedRow q t π γ x := by
  have ht : splitProfile (t 0) (t 1) (t 2 + t 3) (t 2 - t 3) = t := by
    funext s
    fin_cases s <;> simp [splitProfile]
  have hFace : splitProfile (t 0) (t 1) (t 2 + t 3) (t 2 + t 3) = ![t 0, t 1, t 2 + t 3, 0] := by
    funext s
    fin_cases s <;> simp [splitProfile]
  have hd : |t 2 - t 3| ≤ t 2 + t 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [← ht]
  apply weightedRow_split_of_facet hq hd hπ hπeq hγeq
  simpa only [hFace] using hFacet

end HlawkaSchatten.BelowExponent
