/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Mathlib.Data.Sign.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Topology.Instances.Sign
import HlawkaSchatten.Basic

/-!
# Scalar power Bregman data

These are the scalar objects used in the first layer of the audited
Bregman--Mazur proof. The normalization of `powerPotential` is important:
its derivative is the signed `(p - 1)`-power with no extra factor of `p`.
-/

namespace HlawkaSchatten

open Filter
open scoped Topology

/-- The signed real power `sign(x) * |x| ^ q`. -/
noncomputable def signedPower (q x : ℝ) : ℝ :=
  (SignType.sign x : ℝ) * |x| ^ q

/-- The convex scalar potential `|x| ^ p / p`. -/
noncomputable def powerPotential (p x : ℝ) : ℝ :=
  |x| ^ p / p

/-- The signed power that is the gradient of `powerPotential` for `p > 1`. -/
noncomputable def powerGradient (p x : ℝ) : ℝ :=
  |x| ^ (p - 2) * x

/-- The scalar Mazur map used to compare a power geometry with a Hilbert geometry. -/
noncomputable def scalarMazur (p x : ℝ) : ℝ :=
  signedPower (p / 2) x

/-- The Bregman divergence of `powerPotential`, written with its explicit gradient. -/
noncomputable def scalarBregman (p a b : ℝ) : ℝ :=
  powerPotential p a - powerPotential p b - powerGradient p b * (a - b)

@[simp]
theorem signedPower_zero (q : ℝ) : signedPower q 0 = 0 := by
  simp [signedPower]

@[simp]
theorem powerPotential_zero (p : ℝ) : powerPotential p 0 = 0 := by
  by_cases hp : p = 0 <;> simp [powerPotential, hp]

@[simp]
theorem powerGradient_zero (p : ℝ) : powerGradient p 0 = 0 := by
  simp [powerGradient]

/-- Away from the presentation at zero, the gradient is the signed `(p - 1)`-power. -/
theorem powerGradient_eq_signedPower (p x : ℝ) :
    powerGradient p x = signedPower (p - 1) x := by
  by_cases hx : x = 0
  · subst x
    simp
  · have habs : 0 < |x| := abs_pos.mpr hx
    have hpow : |x| ^ (p - 1) = |x| ^ (p - 2) * |x| := by
      calc
        |x| ^ (p - 1) = |x| ^ ((p - 2) + 1) := by congr 1; ring
        _ = |x| ^ (p - 2) * |x| ^ (1 : ℝ) := Real.rpow_add habs _ _
        _ = |x| ^ (p - 2) * |x| := by rw [Real.rpow_one]
    change |x| ^ (p - 2) * x = (SignType.sign x : ℝ) * |x| ^ (p - 1)
    rw [hpow]
    calc
      |x| ^ (p - 2) * x =
          |x| ^ (p - 2) * ((SignType.sign x : ℝ) * |x|) := by rw [sign_mul_abs]
      _ = (SignType.sign x : ℝ) * (|x| ^ (p - 2) * |x|) := by ring

@[simp]
theorem scalarMazur_zero (p : ℝ) : scalarMazur p 0 = 0 := by
  simp [scalarMazur]

@[simp]
theorem scalarBregman_self (p a : ℝ) : scalarBregman p a a = 0 := by
  simp [scalarBregman]

@[simp]
theorem signedPower_one (x : ℝ) : signedPower 1 x = x := by
  simp [signedPower]

@[simp]
theorem signedPower_neg (q x : ℝ) : signedPower q (-x) = -signedPower q x := by
  simp [signedPower, Left.sign_neg]

/-- Composition of signed real powers multiplies their exponents. -/
theorem signedPower_comp (q r x : ℝ) :
    signedPower q (signedPower r x) = signedPower (q * r) x := by
  by_cases hx : x = 0
  · subst x
    simp
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have habs : 0 < |x| := abs_pos.mpr hx
    have hpow : 0 < |x| ^ r := Real.rpow_pos_of_pos habs r
    simp only [signedPower, sign_neg hxneg, SignType.coe_neg,
      SignType.coe_one, neg_mul, one_mul]
    rw [sign_neg (neg_lt_zero.mpr hpow), SignType.coe_neg,
      SignType.coe_one, neg_mul, one_mul, abs_neg, abs_of_pos hpow,
      ← Real.rpow_mul habs.le]
    congr 2
    ring
  · have hpow : 0 < |x| ^ r :=
      Real.rpow_pos_of_pos (abs_pos.mpr hx) r
    simp only [signedPower, sign_pos hxpos, SignType.coe_one, one_mul]
    rw [sign_pos hpow, SignType.coe_one, one_mul, abs_of_pos hpow,
      ← Real.rpow_mul (abs_nonneg x)]
    congr 1
    ring

@[simp]
theorem powerPotential_neg (p x : ℝ) : powerPotential p (-x) = powerPotential p x := by
  simp [powerPotential]

@[simp]
theorem powerGradient_neg (p x : ℝ) : powerGradient p (-x) = -powerGradient p x := by
  rw [powerGradient_eq_signedPower, powerGradient_eq_signedPower, signedPower_neg]

@[simp]
theorem scalarMazur_neg (p x : ℝ) : scalarMazur p (-x) = -scalarMazur p x := by
  simp [scalarMazur]

@[simp]
theorem scalarBregman_neg (p a b : ℝ) :
    scalarBregman p (-a) (-b) = scalarBregman p a b := by
  simp only [scalarBregman, powerPotential_neg, powerGradient_neg]
  ring

/-- Signed positive powers are strictly increasing. -/
theorem strictMono_signedPower {q : ℝ} (hq : 0 < q) : StrictMono (signedPower q) := by
  intro x y hxy
  by_cases hx : x < 0
  · by_cases hy : y < 0
    · have hpow := Real.rpow_lt_rpow (neg_nonneg.mpr hy.le) (neg_lt_neg hxy) hq
      simp only [signedPower, sign_neg hx, sign_neg hy, SignType.coe_neg,
        SignType.coe_one, neg_mul, one_mul, abs_of_neg hx, abs_of_neg hy]
      linarith
    · have hy0 : 0 ≤ y := le_of_not_gt hy
      have hxpow : 0 < (-x) ^ q := Real.rpow_pos_of_pos (neg_pos.mpr hx) q
      simp only [signedPower, sign_neg hx, SignType.coe_neg, SignType.coe_one, neg_mul,
        one_mul, abs_of_neg hx]
      have hynonneg : 0 ≤ (SignType.sign y : ℝ) * |y| ^ q := by
        rcases hy0.eq_or_lt with rfl | hypos
        · simp
        · rw [sign_pos hypos]
          simp only [SignType.coe_one, one_mul]
          exact Real.rpow_nonneg (abs_nonneg y) q
      linarith
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    have hy : 0 < y := hx0.trans_lt hxy
    rcases hx0.eq_or_lt with rfl | hxpos
    · simp only [signedPower, sign_zero, SignType.coe_zero, zero_mul, sign_pos hy,
        SignType.coe_one, one_mul]
      exact Real.rpow_pos_of_pos (abs_pos.mpr hy.ne') q
    · have hpow := Real.rpow_lt_rpow hxpos.le hxy hq
      simpa [signedPower, sign_pos hxpos, sign_pos hy, abs_of_pos hxpos, abs_of_pos hy]
        using hpow

/-- Signed positive powers are continuous, including at the origin. -/
theorem continuous_signedPower {q : ℝ} (hq : 0 < q) : Continuous (signedPower q) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [ContinuousAt, signedPower_zero, tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun y : ℝ ↦ |y| ^ q) (𝓝 0) (𝓝 0) := by
      have hcont : ContinuousAt (fun y : ℝ ↦ |y| ^ q) 0 :=
        continuous_abs.continuousAt.rpow_const (Or.inr hq.le)
      simpa [Real.zero_rpow hq.ne'] using hcont.tendsto
    apply hlim.congr'
    apply Eventually.of_forall
    intro y
    by_cases hy : y = 0
    · subst y
      simp [signedPower, Real.zero_rpow hq.ne']
    · rcases lt_or_gt_of_ne hy with hyneg | hypos
      · simp only [signedPower, sign_neg hyneg, SignType.coe_neg, SignType.coe_one,
          neg_mul, one_mul, norm_neg, Real.norm_eq_abs]
        exact (abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) q)).symm
      · simp only [signedPower, sign_pos hypos, SignType.coe_one, one_mul, Real.norm_eq_abs]
        exact (abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) q)).symm
  · have hsign : ContinuousAt (fun y : ℝ ↦ (SignType.sign y : ℝ)) x := by
      have hcoe : Continuous fun s : SignType ↦ (s : ℝ) :=
        continuous_of_discreteTopology
      exact hcoe.continuousAt.comp (continuousAt_sign_of_ne_zero hx)
    exact hsign.mul (continuous_abs.continuousAt.rpow_const (Or.inl (abs_ne_zero.mpr hx)))

@[simp]
theorem powerGradient_two (x : ℝ) : powerGradient 2 x = x := by
  norm_num [powerGradient]

@[simp]
theorem scalarMazur_two (x : ℝ) : scalarMazur 2 x = x := by
  simp [scalarMazur]

theorem powerPotential_two (x : ℝ) : powerPotential 2 x = x ^ 2 / 2 := by
  simp [powerPotential]

/-- An absolute real power factors through the square of its argument. -/
theorem sq_rpow_div_two (p x : ℝ) :
    (x ^ 2) ^ (p / 2) = |x| ^ p := by
  rw [Real.rpow_div_two_eq_sqrt p (sq_nonneg x), Real.sqrt_sq_eq_abs]

/-- The power potential is an even function expressed through a nonnegative
square. -/
theorem powerPotential_eq_sq_rpow_div_two (p x : ℝ) :
    powerPotential p x = (x ^ 2) ^ (p / 2) / p := by
  rw [powerPotential, sq_rpow_div_two]

/-- At the Hilbert exponent, the scalar Bregman divergence is half a square. -/
theorem scalarBregman_two (a b : ℝ) :
    scalarBregman 2 a b = (a - b) ^ 2 / 2 := by
  rw [scalarBregman, powerPotential_two, powerPotential_two, powerGradient_two]
  ring

/-- Convexity of the scalar power potential before its positive rescaling. -/
theorem convexOn_abs_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ p) := by
  have hImage : (norm : ℝ → ℝ) '' Set.univ = Set.Ici 0 := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact norm_nonneg x
    · intro hy
      have hy' : 0 ≤ y := by simpa only [Set.mem_Ici] using hy
      exact ⟨y, Set.mem_univ y, by simp [abs_of_nonneg hy']⟩
  have hOuter : ConvexOn ℝ ((norm : ℝ → ℝ) '' Set.univ) (fun y : ℝ ↦ y ^ p) := by
    rw [hImage]
    exact convexOn_rpow hp
  have hMono : MonotoneOn (fun y : ℝ ↦ y ^ p) ((norm : ℝ → ℝ) '' Set.univ) := by
    rw [hImage]
    exact (Real.strictMonoOn_rpow_Ici_of_exponent_pos (zero_lt_one.trans_le hp)).monotoneOn
  convert hOuter.comp convexOn_univ_norm hMono using 1
  ext x
  simp only [Function.comp_apply, Real.norm_eq_abs]

/-- For exponent greater than one, the absolute-value power is strictly convex. -/
theorem strictConvexOn_abs_rpow {p : ℝ} (hp : 1 < p) :
    StrictConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ p) := by
  have hcont : Continuous (fun x : ℝ ↦ |x| ^ p) := by
    have hdiff : Differentiable ℝ (fun x : ℝ ↦ ‖x‖ ^ p) :=
      differentiable_norm_rpow hp
    simpa only [Real.norm_eq_abs] using hdiff.continuous
  apply StrictMono.strictConvexOn_univ_of_deriv hcont
  have hderiv : deriv (fun x : ℝ ↦ |x| ^ p) = fun x ↦ p * powerGradient p x := by
    funext x
    rw [(hasDerivAt_abs_rpow x hp).deriv]
    unfold powerGradient
    ring
  rw [hderiv]
  have hgrad : StrictMono (powerGradient p) := by
    intro x y hxy
    rw [powerGradient_eq_signedPower, powerGradient_eq_signedPower]
    exact strictMono_signedPower (sub_pos.mpr hp) hxy
  exact hgrad.const_mul (zero_lt_one.trans hp)

/-- Strict convexity of `|x|^p` gives nonnegativity of its Bregman divergence. -/
theorem scalarBregman_nonneg {p : ℝ} (hp : 1 < p) (a b : ℝ) :
    0 ≤ scalarBregman p a b := by
  have hSupport :
      p * powerGradient p b * (a - b) ≤ |a| ^ p - |b| ^ p := by
    rcases lt_trichotomy a b with hab | rfl | hba
    · have hSlope := (convexOn_abs_rpow hp.le).slope_le_of_hasDerivAt
          (Set.mem_univ a) (Set.mem_univ b) hab (hasDerivAt_abs_rpow b hp)
      rw [slope_def_field] at hSlope
      have hMul := (div_le_iff₀ (sub_pos.mpr hab)).mp hSlope
      unfold powerGradient
      nlinarith
    · simp
    · have hSlope := (convexOn_abs_rpow hp.le).le_slope_of_hasDerivAt
          (Set.mem_univ b) (Set.mem_univ a) hba (hasDerivAt_abs_rpow b hp)
      rw [slope_def_field] at hSlope
      have hMul := (le_div_iff₀ (sub_pos.mpr hba)).mp hSlope
      unfold powerGradient
      nlinarith
  rw [show scalarBregman p a b =
      (|a| ^ p - |b| ^ p - p * powerGradient p b * (a - b)) / p by
    unfold scalarBregman powerPotential
    field_simp [hp.ne']
    ]
  exact div_nonneg (sub_nonneg.mpr hSupport) (zero_lt_one.trans hp).le

/-- The scalar Bregman divergence is strictly positive off the diagonal. -/
theorem scalarBregman_pos {p : ℝ} (hp : 1 < p) {a b : ℝ} (hab : a ≠ b) :
    0 < scalarBregman p a b := by
  have hSupport :
      p * powerGradient p b * (a - b) < |a| ^ p - |b| ^ p := by
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have hSlope := (strictConvexOn_abs_rpow hp).slope_lt_of_hasDerivAt
          (Set.mem_univ a) (Set.mem_univ b) hlt (hasDerivAt_abs_rpow b hp)
      rw [slope_def_field] at hSlope
      have hMul := (div_lt_iff₀ (sub_pos.mpr hlt)).mp hSlope
      unfold powerGradient
      nlinarith
    · exact (hab heq).elim
    · have hSlope := (strictConvexOn_abs_rpow hp).lt_slope_of_hasDerivAt
          (Set.mem_univ b) (Set.mem_univ a) hgt (hasDerivAt_abs_rpow b hp)
      rw [slope_def_field] at hSlope
      have hMul := (lt_div_iff₀ (sub_pos.mpr hgt)).mp hSlope
      unfold powerGradient
      nlinarith
  rw [show scalarBregman p a b =
      (|a| ^ p - |b| ^ p - p * powerGradient p b * (a - b)) / p by
    unfold scalarBregman powerPotential
    field_simp [hp.ne']]
  exact div_pos (sub_pos.mpr hSupport) (zero_lt_one.trans hp)

theorem scalarBregman_eq_zero_iff {p : ℝ} (hp : 1 < p) (a b : ℝ) :
    scalarBregman p a b = 0 ↔ a = b := by
  constructor
  · intro hzero
    by_contra hab
    exact (scalarBregman_pos hp hab).ne' hzero
  · intro hab
    subst b
    exact scalarBregman_self p a

/-- The power potential is homogeneous under positive scalar multiplication. -/
theorem powerPotential_mul_of_pos (p x : ℝ) {c : ℝ} (hc : 0 < c) :
    powerPotential p (c * x) = c ^ p * powerPotential p x := by
  simp only [powerPotential, abs_mul, abs_of_pos hc, Real.mul_rpow hc.le (abs_nonneg x)]
  ring

/-- Signed powers have their expected homogeneity for a positive scalar. -/
theorem signedPower_mul_of_pos (q x : ℝ) {c : ℝ} (hc : 0 < c) :
    signedPower q (c * x) = c ^ q * signedPower q x := by
  simp only [signedPower, sign_mul, sign_pos hc, one_mul, abs_mul,
    abs_of_pos hc, Real.mul_rpow hc.le (abs_nonneg x)]
  ring

/-- The scalar Mazur map has degree `p / 2`. -/
theorem scalarMazur_mul_of_pos (p x : ℝ) {c : ℝ} (hc : 0 < c) :
    scalarMazur p (c * x) = c ^ (p / 2) * scalarMazur p x := by
  exact signedPower_mul_of_pos (p / 2) x hc

/-- The normalized power gradient has degree `p - 1`. -/
theorem powerGradient_mul_of_pos (p x : ℝ) {c : ℝ} (hc : 0 < c) :
    powerGradient p (c * x) = c ^ (p - 1) * powerGradient p x := by
  have hpow : c ^ (p - 1) = c ^ (p - 2) * c := by
    calc
      c ^ (p - 1) = c ^ ((p - 2) + 1) := by congr 1; ring
      _ = c ^ (p - 2) * c ^ (1 : ℝ) := Real.rpow_add hc _ _
      _ = c ^ (p - 2) * c := by rw [Real.rpow_one]
  simp only [powerGradient, abs_mul, abs_of_pos hc,
    Real.mul_rpow hc.le (abs_nonneg x), hpow]
  ring

/-- Euler's identity for the homogeneous power potential. -/
theorem powerGradient_mul_self {p : ℝ} (hp : 0 < p) (x : ℝ) :
    powerGradient p x * x = p * powerPotential p x := by
  by_cases hx : x = 0
  · subst x
    simp
  · have ha : 0 < |x| := abs_pos.mpr hx
    unfold powerGradient powerPotential
    have hs : x * x = |x| ^ (2 : ℕ) := by
      nlinarith [sq_abs x]
    rw [mul_assoc, hs]
    rw [show |x| ^ (2 : ℕ) = |x| ^ (2 : ℝ) by norm_num,
      ← Real.rpow_add ha]
    rw [show p - 2 + 2 = p by ring]
    field_simp [hp.ne']

/-- The scalar Bregman divergence has degree `p` under positive common scaling. -/
theorem scalarBregman_mul_of_pos (p a b : ℝ) {c : ℝ} (hc : 0 < c) :
    scalarBregman p (c * a) (c * b) = c ^ p * scalarBregman p a b := by
  have hpow : c ^ p = c ^ (p - 1) * c := by
    calc
      c ^ p = c ^ ((p - 1) + 1) := by congr 1; ring
      _ = c ^ (p - 1) * c ^ (1 : ℝ) := Real.rpow_add hc _ _
      _ = c ^ (p - 1) * c := by rw [Real.rpow_one]
  rw [scalarBregman, powerPotential_mul_of_pos p a hc,
    powerPotential_mul_of_pos p b hc, powerGradient_mul_of_pos p b hc]
  unfold scalarBregman
  rw [hpow]
  ring

/-- The scalar Bregman--Mazur comparison is an equality at `p = 2`. -/
theorem scalarBregman_eq_mazur_sq_at_two (a b : ℝ) :
    scalarBregman 2 a b = (scalarMazur 2 a - scalarMazur 2 b) ^ 2 / 2 := by
  simp only [scalarMazur_two, scalarBregman_two]

end HlawkaSchatten
