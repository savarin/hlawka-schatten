/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Interpolation

/-! The common weights and the signed-coordinate identity used in the G1 and G3
facet proofs. The algebraic identities hold for an arbitrary real exponent. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable section

/-- Profile with last-coordinate sum l, first-coordinate difference e, and last-coordinate difference d. -/
def balancedProfile (l e d : ℝ) : Profile :=
  splitProfile ((1 - l + e) / 2) ((1 - l - e) / 2) l d

def balancedPi (μ e : ℝ) : Profile :=
  ![μ * (1 - e) / 2, μ * (1 + e) / 2, (1 - μ) / 2, (1 - μ) / 2]

def balancedGamma (μ l : ℝ) : Row :=
  ![(1 - μ * (1 - l)) / 2, (1 - μ * (1 - l)) / 2, μ * (1 - l)]

/-- The coordinates are x₁ = p + s, −x₂ = p − s, and −x₃ = z. -/
def balancedRow (p s z : ℝ) : Row :=
  ![p + s, -(p - s), -z]

theorem balancedRow_decompose (x : Row) :
    balancedRow ((x 0 - x 1) / 2) ((x 0 + x 1) / 2) (-x 2) = x := by
  funext i
  fin_cases i <;> simp [balancedRow] <;> ring

theorem isSimplex_balancedPi {μ e : ℝ} (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    (he : |e| ≤ 1) : IsSimplex (balancedPi μ e) := by
  obtain ⟨hel, heu⟩ := abs_le.mp he
  have hm : 0 ≤ 1 - μ := sub_nonneg.mpr hμ₁
  have hsub : 0 ≤ 1 - e := sub_nonneg.mpr heu
  have hadd : 0 ≤ 1 + e := by linarith
  constructor
  · intro i
    fin_cases i <;> simp [balancedPi] <;> positivity
  · simp [balancedPi, Fin.sum_univ_four]
    ring

theorem balancedGamma_sum (μ l : ℝ) : (∑ j, balancedGamma μ l j) = 1 := by
  simp [balancedGamma, Fin.sum_univ_three]

theorem balancedGamma_nonneg {μ l : ℝ} (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    (hl₀ : 0 ≤ l) (hl₁ : l ≤ 1) (j : Fin 3) : 0 ≤ balancedGamma μ l j := by
  have hl : 0 ≤ 1 - l := sub_nonneg.mpr hl₁
  have hprod : μ * (1 - l) ≤ 1 := calc
    _ ≤ 1 * (1 - l) := mul_le_mul_of_nonneg_right hμ₁ hl
    _ ≤ 1 := by linarith
  have hrest : 0 ≤ 1 - μ * (1 - l) := sub_nonneg.mpr hprod
  fin_cases j <;> simp [balancedGamma] <;> positivity

def balancedFarCenter (l d p z : ℝ) : ℝ :=
  (1 - l) * z + d * p

def balancedNearShift (l e d p s z : ℝ) : ℝ :=
  e * s + l * z - d * p

theorem balancedNearShift_facet (l e p s z : ℝ) :
    balancedNearShift l e l p s z = e * s + l * (z - p) := by
  unfold balancedNearShift
  ring

/-- The four exact row outputs before taking absolute values. -/
theorem rowEval_balancedProfile (l e d p s z : ℝ) (i : Fin 4) :
    rowEval (balancedProfile l e d) i (balancedRow p s z) =
      ![-(balancedFarCenter l d p z - (1 + e) * s),
        -(balancedFarCenter l d p z + (1 - e) * s),
        -(p - balancedNearShift l e d p s z),
        p + balancedNearShift l e d p s z] i := by
  fin_cases i <;> simp (config := { decide := true })
    [rowEval, balancedProfile, splitProfile, balancedRow, sign, partner,
      balancedFarCenter, balancedNearShift, Fin.sum_univ_three] <;> ring

/-- The centered even difference A(p,s) of the absolute q-th power. -/
def balancedEvenGap (q p s : ℝ) : ℝ :=
  (|p + s| ^ q + |p - s| ^ q) / 2 - |p| ^ q

/-- The two-point Jensen gap J between z and p on the upper facet. -/
def balancedJensenGap (q l p z : ℝ) : ℝ :=
  (1 - l) * |z| ^ q + l * |p| ^ q - |balancedFarCenter l l p z| ^ q

/-- The centered increment H of the far pair. -/
def balancedFarIncrement (q e Z s : ℝ) : ℝ :=
  ((1 - e) / 2) * |Z - (1 + e) * s| ^ q +
    ((1 + e) / 2) * |Z + (1 - e) * s| ^ q - |Z| ^ q

/-- The scalar gap N−L in the G1 and G3 hand proofs. -/
def balancedFacetGap (q μ l e p s z : ℝ) : ℝ :=
  μ * balancedJensenGap q l p z +
    (1 - μ * (1 - l)) * balancedEvenGap q p s -
    (1 - μ) * balancedEvenGap q p (balancedNearShift l e l p s z) -
    μ * balancedFarIncrement q e (balancedFarCenter l l p z) s

/-- The G3 normalization uses h = 1 − e and l = h k. -/
theorem balancedFacetGap_div_h (q μ h k p s z : ℝ) (hh : h ≠ 0) (hk : k ≠ 0) :
    balancedFacetGap q μ (h * k) (1 - h) p s z / h =
      μ * k * (balancedJensenGap q (h * k) p z / (h * k) + balancedEvenGap q p s) +
        (1 - μ) * (balancedEvenGap q p s -
          balancedEvenGap q p (balancedNearShift (h * k) (1 - h) (h * k) p s z)) / h -
        μ * balancedFarIncrement q (1 - h) (balancedFarCenter (h * k) (h * k) p z) s / h := by
  unfold balancedFacetGap
  field_simp
  ring

theorem balanced_facet_gap_eq (q μ l e p s z : ℝ) :
    (∑ j, balancedGamma μ l j * |balancedRow p s z j| ^ q) -
      (∑ i, balancedPi μ e i * |rowEval (balancedProfile l e l) i (balancedRow p s z)| ^ q) =
      balancedFacetGap q μ l e p s z := by
  simp only [Fin.sum_univ_three, Fin.sum_univ_four, rowEval_balancedProfile]
  simp only [balancedGamma, balancedPi, balancedRow, balancedFacetGap, balancedJensenGap,
    balancedEvenGap, balancedFarIncrement, Matrix.cons_val, abs_neg]
  ring

theorem weightedRow_balancedFacet_iff (q μ l e p s z : ℝ) :
    WeightedRow q (balancedProfile l e l) (balancedPi μ e) (balancedGamma μ l)
      (balancedRow p s z) ↔ 0 ≤ balancedFacetGap q μ l e p s z := by
  rw [← balanced_facet_gap_eq]
  exact sub_nonneg.symm

/-- A scalar gap proof on the upper facet gives a certificate for the original profile. -/
theorem rowAt_of_balancedFacetGap {q μ : ℝ} {t : Profile} (hq : 1 ≤ q)
    (ht : IsSimplex t) (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    (hgap : ∀ p s z, 0 ≤ balancedFacetGap q μ (t 2 + t 3) (t 0 - t 1) p s z) :
    RowAt q t := by
  have hsum : t 0 + t 1 + t 2 + t 3 = 1 := by
    simpa only [Fin.sum_univ_four] using ht.2
  have hnum₀ := ht.1 0
  have hnum₁ := ht.1 1
  have hnum₂ := ht.1 2
  have hnum₃ := ht.1 3
  have hl₀ : 0 ≤ t 2 + t 3 := add_nonneg hnum₂ hnum₃
  have hl₁ : t 2 + t 3 ≤ 1 := by linarith
  have he : |t 0 - t 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hπ := isSimplex_balancedPi hμ₀ hμ₁ he
  refine ⟨balancedPi μ _, hπ, balancedGamma μ _, balancedGamma_nonneg hμ₀ hμ₁ hl₀ hl₁,
    (balancedGamma_sum _ _).le, ?_⟩
  apply weightedRow_of_lastFacet hq hnum₂ hnum₃ hπ.1 (by rfl) (by rfl)
  have hProfile : balancedProfile (t 2 + t 3) (t 0 - t 1) (t 2 + t 3) =
      ![t 0, t 1, t 2 + t 3, 0] := by
    funext i
    fin_cases i <;> simp [balancedProfile, splitProfile] <;> linarith
  intro x
  rw [← hProfile, ← balancedRow_decompose x]
  exact (weightedRow_balancedFacet_iff _ _ _ _ _ _ _).2 (hgap _ _ _)

private theorem balancedRow_scale (a p s z : ℝ) :
    balancedRow (a * p) (a * s) (a * z) = a • balancedRow p s z := by
  funext i
  fin_cases i <;> simp [balancedRow, Pi.smul_apply] <;> ring

theorem balancedFacetGap_nonneg_scale_iff {a : ℝ} (ha : a ≠ 0) (q μ l e p s z : ℝ) :
    0 ≤ balancedFacetGap q μ l e (a * p) (a * s) (a * z) ↔
      0 ≤ balancedFacetGap q μ l e p s z := by
  rw [← weightedRow_balancedFacet_iff q μ l e (a * p) (a * s) (a * z),
    ← weightedRow_balancedFacet_iff q μ l e p s z, balancedRow_scale, weightedRow_smul_iff ha]

/-- The three bounded charts in G3 imply the gap inequality on every row. -/
theorem balancedFacetGap_nonneg_of_charts {q μ l e : ℝ} (hq : 0 < q)
    (hHead : ∀ p s, |p| ≤ 1/8 → |s| ≤ 1/8 → 0 ≤ balancedFacetGap q μ l e p s 1)
    (hP : ∀ s z, |s| ≤ 1 → |z| ≤ 8 → 0 ≤ balancedFacetGap q μ l e 1 s z)
    (hS : ∀ p z, |p| ≤ 1 → |z| ≤ 8 → 0 ≤ balancedFacetGap q μ l e p 1 z) :
    ∀ p s z, 0 ≤ balancedFacetGap q μ l e p s z := by
  intro p s z
  by_cases hzero : p = 0 ∧ s = 0 ∧ z = 0
  · obtain ⟨rfl, rfl, rfl⟩ := hzero
    simp [balancedFacetGap, balancedEvenGap, balancedJensenGap, balancedFarIncrement,
      balancedFarCenter, balancedNearShift, Real.zero_rpow hq.ne']
  have hpMax : |p| ≤ max |p| |s| := le_max_left ..
  have hsMax : |s| ≤ max |p| |s| := le_max_right ..
  by_cases hfar : 8 * max |p| |s| ≤ |z|
  · have hz : z ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at hfar
      exact hzero ⟨abs_eq_zero.mp (le_antisymm (by linarith) (abs_nonneg p)),
        abs_eq_zero.mp (le_antisymm (by linarith) (abs_nonneg s)), hz⟩
    have hp : |p / z| ≤ 1/8 := by
      rw [abs_div]
      exact (div_le_iff₀ (abs_pos.mpr hz)).2 (by linarith)
    have hs : |s / z| ≤ 1/8 := by
      rw [abs_div]
      exact (div_le_iff₀ (abs_pos.mpr hz)).2 (by linarith)
    simpa only [mul_div_cancel₀ _ hz, mul_one] using
      (balancedFacetGap_nonneg_scale_iff hz q μ l e (p / z) (s / z) 1).mpr (hHead _ _ hp hs)
  have hnear := lt_of_not_ge hfar
  by_cases hsp : |s| ≤ |p|
  · rw [max_eq_left hsp] at hnear
    have hp : p ≠ 0 := by
      intro hp
      rw [hp, abs_zero, mul_zero] at hnear
      exact (not_lt_of_ge (abs_nonneg z)) hnear
    have hs : |s / p| ≤ 1 := by
      rw [abs_div]
      exact (div_le_one (abs_pos.mpr hp)).2 hsp
    have hz : |z / p| ≤ 8 := by
      rw [abs_div]
      exact (div_le_iff₀ (abs_pos.mpr hp)).2 hnear.le
    simpa only [mul_div_cancel₀ _ hp, mul_one] using
      (balancedFacetGap_nonneg_scale_iff hp q μ l e 1 (s / p) (z / p)).mpr (hP _ _ hs hz)
  · have hps := lt_of_not_ge hsp
    rw [max_eq_right hps.le] at hnear
    have hs : s ≠ 0 := by
      intro hs
      rw [hs, abs_zero, mul_zero] at hnear
      exact (not_lt_of_ge (abs_nonneg z)) hnear
    have hp : |p / s| ≤ 1 := by
      rw [abs_div]
      exact (div_le_one (abs_pos.mpr hs)).2 hps.le
    have hz : |z / s| ≤ 8 := by
      rw [abs_div]
      exact (div_le_iff₀ (abs_pos.mpr hs)).2 hnear.le
    simpa only [mul_div_cancel₀ _ hs, mul_one] using
      (balancedFacetGap_nonneg_scale_iff hs q μ l e (p / s) 1 (z / s)).mpr (hS _ _ hp hz)

/-- At fixed e and μ, the G1 upper-facet gap follows from the two length endpoints. -/
theorem balancedFacetGap_nonneg_lerp {q μ e l₀ l₁ a p s z : ℝ}
    (hq : 1 ≤ q) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1) (he : |e| ≤ 1)
    (h₀ : 0 ≤ balancedFacetGap q μ l₀ e p s z)
    (h₁ : 0 ≤ balancedFacetGap q μ l₁ e p s z) :
    0 ≤ balancedFacetGap q μ ((1 - a) * l₀ + a * l₁) e p s z := by
  let l := (1 - a) * l₀ + a * l₁
  have ht : balancedProfile l e l =
      profileLerp a (balancedProfile l₀ e l₀) (balancedProfile l₁ e l₁) := by
    funext i
    fin_cases i <;> simp [balancedProfile, splitProfile, profileLerp, l] <;> ring
  have hγ : balancedGamma μ l = rowLerp a (balancedGamma μ l₀) (balancedGamma μ l₁) := by
    funext j
    fin_cases j <;> simp [balancedGamma, rowLerp, l] <;> ring
  apply (weightedRow_balancedFacet_iff q μ l e p s z).1
  rw [ht, hγ]
  exact weightedRow_profileLerp hq ha₀ ha₁ (isSimplex_balancedPi hμ₀ hμ₁ he).1
    ((weightedRow_balancedFacet_iff q μ l₀ e p s z).2 h₀)
    ((weightedRow_balancedFacet_iff q μ l₁ e p s z).2 h₁)

end

end HlawkaSchatten.BelowExponent
