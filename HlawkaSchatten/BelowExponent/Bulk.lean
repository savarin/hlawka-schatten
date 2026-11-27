/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Interpolation
public import HlawkaSchatten.BelowExponent.Exponents
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-! Power enclosures and integer corner comparisons for the fixed bulk certificate. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

/-- The exponent bracket used by the bulk power tables. -/
theorem criticalQ_bulk_bracket : 1054 / 665 < criticalQ ∧ criticalQ < 3647 / 2301 := by
  refine ⟨criticalQ_bracket.1, ?_⟩
  apply (lt_div_iff₀ (by norm_num : 0 < (2301 : ℝ))).2
  apply (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).1
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), two_rpow_criticalQ]
  change (3 : ℝ) ^ ((2301 : ℕ) : ℝ) < (2 : ℝ) ^ ((3647 : ℕ) : ℝ)
  rw [Real.rpow_natCast, Real.rpow_natCast]
  exact_mod_cast (by decide +kernel : (3 : ℕ) ^ 2301 < (2 : ℕ) ^ 3647)

private theorem rpow_natFraction_pow {x : ℝ} (hx : 0 ≤ x) (m : ℕ) {n : ℕ} (hn : 0 < n) :
    (x ^ ((m : ℝ) / (n : ℝ))) ^ n = x ^ m := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← Real.rpow_natCast (x ^ ((m : ℝ) / (n : ℝ))) n, ← Real.rpow_mul hx,
    div_mul_cancel₀ _ hn', Real.rpow_natCast]

theorem rpow_natFraction_le_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {m n : ℕ} (hn : 0 < n) :
    x ^ ((m : ℝ) / (n : ℝ)) ≤ y ↔ x ^ m ≤ y ^ n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := Real.rpow_le_rpow_iff (Real.rpow_nonneg hx ((m : ℝ) / (n : ℝ))) hy hn'
  rw [Real.rpow_natCast, Real.rpow_natCast, rpow_natFraction_pow hx m hn] at h
  exact h.symm

theorem le_rpow_natFraction_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {m n : ℕ} (hn : 0 < n) :
    y ≤ x ^ ((m : ℝ) / (n : ℝ)) ↔ y ^ n ≤ x ^ m := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := Real.rpow_le_rpow_iff hy (Real.rpow_nonneg hx ((m : ℝ) / (n : ℝ))) hn'
  rw [Real.rpow_natCast, Real.rpow_natCast, rpow_natFraction_pow hx m hn] at h
  exact h.symm

/-- An upper power-table entry is equivalent to a natural-number cross-power comparison. -/
theorem natRat_rpow_le_iff {a b c d m n : ℕ} (hb : 0 < b) (hd : 0 < d) (hn : 0 < n) :
    ((a : ℝ) / (b : ℝ)) ^ ((m : ℝ) / (n : ℝ)) ≤ (c : ℝ) / (d : ℝ) ↔
      a ^ m * d ^ n ≤ c ^ n * b ^ m := by
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [rpow_natFraction_le_iff (by positivity) (by positivity) hn, div_pow, div_pow,
    div_le_div_iff₀ (pow_pos hb' m) (pow_pos hd' n)]
  norm_cast

/-- A lower power-table entry uses the reverse natural-number comparison. -/
theorem le_natRat_rpow_iff {a b c d m n : ℕ} (hb : 0 < b) (hd : 0 < d) (hn : 0 < n) :
    (c : ℝ) / (d : ℝ) ≤ ((a : ℝ) / (b : ℝ)) ^ ((m : ℝ) / (n : ℝ)) ↔
      c ^ n * b ^ m ≤ a ^ m * d ^ n := by
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [le_rpow_natFraction_iff (by positivity) (by positivity) hn, div_pow, div_pow,
    div_le_div_iff₀ (pow_pos hd' n) (pow_pos hb' m)]
  norm_cast

/-- Select the exponent endpoint according to which side of one the base lies on. -/
theorem rpow_exponent_bounds {x q lo hi : ℝ} (hx : 0 ≤ x) (hlo₀ : 0 ≤ lo)
    (hlo : lo ≤ q) (hhi : q ≤ hi) :
    (if x ≤ 1 then x ^ hi else x ^ lo) ≤ x ^ q ∧
      x ^ q ≤ (if x ≤ 1 then x ^ lo else x ^ hi) := by
  by_cases hx₁ : x ≤ 1
  · simp only [ite_eq_left hx₁]
    exact ⟨Real.rpow_le_rpow_of_exponent_ge' hx hx₁ (hlo₀.trans hlo) hhi,
      Real.rpow_le_rpow_of_exponent_ge' hx hx₁ hlo₀ hlo⟩
  · simp only [ite_eq_right hx₁]
    have hx' : 1 ≤ x := (lt_of_not_ge hx₁).le
    exact ⟨Real.rpow_le_rpow_of_exponent_le hx' hlo, Real.rpow_le_rpow_of_exponent_le hx' hhi⟩

/-- An upper chord remains valid when the tabulated powers are rounded outward. -/
theorem rpow_le_upperChord {q a b y u upperA upperB : ℝ} (hq : 1 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hy : 0 ≤ y) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1)
    (hY : y ≤ (1 - u) * a + u * b) (hA : a ^ q ≤ upperA) (hB : b ^ q ≤ upperB) :
    y ^ q ≤ (1 - u) * upperA + u * upperB := by
  have hu : 0 ≤ 1 - u := sub_nonneg.mpr hu₁
  calc
    _ ≤ ((1 - u) * a + u * b) ^ q := Real.rpow_le_rpow hy hY (zero_le_one.trans hq)
    _ ≤ (1 - u) * a ^ q + u * b ^ q := by
      simpa only [smul_eq_mul] using (convexOn_rpow hq).2
        (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb) hu hu₀ (sub_add_cancel 1 u)
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hA hu) (mul_le_mul_of_nonneg_left hB hu₀)

/-- The tangent on a nonnegative row interval is a lower bound for the power. -/
theorem tangent_le_rpow {q m y : ℝ} (hq : 1 ≤ q) (hm : 0 < m) (hy : 0 ≤ y) :
    m ^ q + (q * m ^ (q - 1)) * (y - m) ≤ y ^ q := by
  have hConv := convexOn_rpow hq
  have hDeriv := Real.hasDerivAt_rpow_const (x := m) (p := q) (Or.inl hm.ne')
  have hm' : m ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hm.le
  have hy' : y ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hy
  rcases lt_trichotomy y m with hlt | rfl | hgt
  · have h := hConv.slope_le_of_hasDerivAt hy' hm' hlt hDeriv
    rw [slope_def_field] at h
    have h' := (div_le_iff₀ (sub_pos.mpr hlt)).mp h
    nlinarith only [h']
  · simp
  · have h := hConv.le_slope_of_hasDerivAt hm' hy' hgt hDeriv
    rw [slope_def_field] at h
    have h' := (le_div_iff₀ (sub_pos.mpr hgt)).mp h
    nlinarith only [h']

/-- The tangent form used by the finite input table. -/
theorem tangentRatio_le_rpow {q m y : ℝ} (hq : 1 ≤ q) (hm : 0 < m) (hy : 0 ≤ y) :
    m ^ q * (1 + q * (y / m - 1)) ≤ y ^ q := by
  have h := tangent_le_rpow hq hm hy
  rw [Real.rpow_sub hm, Real.rpow_one] at h
  convert h using 1
  field_simp [hm.ne']

/-- Lower endpoint values below an affine function remain below it after interpolation. -/
theorem sum_le_affine_barycenter {ι : Type*} {vertices : Finset ι} {w coord lower : ι → ℝ}
    {m b : ℝ} (hw : ∀ i ∈ vertices, 0 ≤ w i) (hSum : ∑ i ∈ vertices, w i = 1)
    (hLower : ∀ i ∈ vertices, lower i ≤ m * coord i + b) :
    (∑ i ∈ vertices, w i * lower i) ≤ m * (∑ i ∈ vertices, w i * coord i) + b := by
  calc
    _ ≤ ∑ i ∈ vertices, w i * (m * coord i + b) :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hLower i hi) (hw i hi)
    _ = (∑ i ∈ vertices, m * (w i * coord i)) + ∑ i ∈ vertices, w i * b := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul, hSum, one_mul]

/-- Compare the two integer dot products at a row-grid corner. Input bounds can be negative. -/
def bulkCornerOK (p : Fin 4 → ℕ) (g : Fin 3 → ℕ) (upper : Fin 4 → ℤ) (lower : Fin 3 → ℤ) :
    Bool :=
  decide ((∑ s, (p s : ℤ) * upper s) ≤ ∑ j, (g j : ℤ) * lower j)

/-- A successful integer comparison bounds the actual output by the affine input table values. -/
theorem bulkCornerOK_sound {q : ℝ} {t : Profile} {x : Row}
    {p : Fin 4 → ℕ} {g : Fin 3 → ℕ} {upper : Fin 4 → ℤ} {lower : Fin 3 → ℤ}
    {weightDen valueDen : ℕ} (hW : 0 < (weightDen : ℝ)) (hV : 0 < (valueDen : ℝ))
    (hUpper : ∀ s, |rowEval t s x| ^ q ≤ (upper s : ℝ) / (valueDen : ℝ))
    (hCheck : bulkCornerOK p g upper lower = true) :
    (∑ s, ((p s : ℝ) / (weightDen : ℝ)) * |rowEval t s x| ^ q) ≤
      ∑ j, ((g j : ℝ) / (weightDen : ℝ)) * ((lower j : ℝ) / (valueDen : ℝ)) := by
  have hInt : (∑ s, (p s : ℤ) * upper s) ≤ ∑ j, (g j : ℤ) * lower j :=
    of_decide_eq_true hCheck
  have hReal : (∑ s, (p s : ℝ) * (upper s : ℝ)) ≤ ∑ j, (g j : ℝ) * (lower j : ℝ) := by
    exact_mod_cast hInt
  calc
    _ ≤ ∑ s, ((p s : ℝ) / (weightDen : ℝ)) * ((upper s : ℝ) / (valueDen : ℝ)) :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hUpper s) (by positivity)
    _ = (∑ s, (p s : ℝ) * (upper s : ℝ)) / ((weightDen : ℝ) * (valueDen : ℝ)) := by
      simp only [div_mul_div_comm, Finset.sum_div]
    _ ≤ (∑ j, (g j : ℝ) * (lower j : ℝ)) / ((weightDen : ℝ) * (valueDen : ℝ)) :=
      div_le_div_of_nonneg_right hReal (mul_nonneg hW.le hV.le)
    _ = _ := by simp only [div_mul_div_comm, Finset.sum_div]

/-- The fixed-point corner checks certify a row interpolated from their vertices. -/
theorem weightedRow_of_bulkCorners {ι : Type*} {q : ℝ} {t : Profile} {vertices : Finset ι}
    {w : ι → ℝ} {x : ι → Row} {p : Fin 4 → ℕ} {g : Fin 3 → ℕ}
    {upper : ι → Fin 4 → ℤ} {lower : ι → Fin 3 → ℤ} {weightDen valueDen : ℕ}
    (hq : 1 ≤ q) (hW : 0 < (weightDen : ℝ)) (hV : 0 < (valueDen : ℝ))
    (hw : ∀ i ∈ vertices, 0 ≤ w i) (hSum : ∑ i ∈ vertices, w i = 1)
    (hUpper : ∀ i ∈ vertices, ∀ s, |rowEval t s (x i)| ^ q ≤
      (upper i s : ℝ) / (valueDen : ℝ))
    (hCheck : ∀ i ∈ vertices, bulkCornerOK p g (upper i) (lower i) = true)
    (hLower : ∀ j, (∑ i ∈ vertices, w i * ((lower i j : ℝ) / (valueDen : ℝ))) ≤
      |(∑ i ∈ vertices, w i • x i) j| ^ q) :
    WeightedRow q t (fun s => (p s : ℝ) / (weightDen : ℝ))
      (fun j => (g j : ℝ) / (weightDen : ℝ)) (∑ i ∈ vertices, w i • x i) := by
  refine weightedRow_rowBarycenter hq hw hSum (fun s => by positivity) (fun j => by positivity)
    ?_ hLower
  exact fun i hi => bulkCornerOK_sound hW hV (hUpper i hi) (hCheck i hi)

end HlawkaSchatten.BelowExponent
