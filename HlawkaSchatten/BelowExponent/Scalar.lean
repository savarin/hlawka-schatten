/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Balanced
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-! Scalar estimates for the balanced G1 and G3 certificates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

private theorem absPower_lerp_lt {q u x y : ℝ} (hq : 1 < q) (hu₀ : 0 < u)
    (hu₁ : u < 1) (hxy : x ≠ y) :
    |(1 - u) * x + u * y| ^ q < (1 - u) * |x| ^ q + u * |y| ^ q := by
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hu : 0 < 1 - u := sub_pos.mpr hu₁
  by_cases h : |x| = |y|
  · have hopp : y = -x := by
      rcases abs_eq_abs.mp h with heq | heq
      · exact (hxy heq).elim
      · linarith
    have hx : x ≠ 0 := by
      intro hx
      exact hxy (by rw [hopp, hx, neg_zero])
    have hc : |1 - 2 * u| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hinput : |(1 - u) * x + u * y| < |x| := by
      rw [hopp, show (1 - u) * x + u * -x = (1 - 2 * u) * x by ring, abs_mul]
      simpa only [one_mul] using mul_lt_mul_of_pos_right hc (abs_pos.mpr hx)
    have hrhs : (1 - u) * |x| ^ q + u * |y| ^ q = |x| ^ q := by
      rw [← h]
      ring
    rw [hrhs]
    exact Real.rpow_lt_rpow (abs_nonneg _) hinput hq₀
  · have htriangle : |(1 - u) * x + u * y| ≤ (1 - u) * |x| + u * |y| := by
      simpa only [abs_mul, abs_of_nonneg hu.le, abs_of_nonneg hu₀.le] using
        abs_add_le ((1 - u) * x) (u * y)
    refine (Real.rpow_le_rpow (abs_nonneg _) htriangle hq₀.le).trans_lt ?_
    simpa only [smul_eq_mul] using (strictConvexOn_rpow hq).2
      (Set.mem_Ici.mpr (abs_nonneg x)) (Set.mem_Ici.mpr (abs_nonneg y))
      h hu hu₀ (sub_add_cancel 1 u)

/-- The upper-facet Jensen term is strict for a nontrivial split of distinct coordinates. -/
theorem balancedJensenGap_pos {q l p z : ℝ} (hq : 1 < q) (hl₀ : 0 < l) (hl₁ : l < 1)
    (hzp : z ≠ p) : 0 < balancedJensenGap q l p z :=
  sub_pos.mpr (absPower_lerp_lt hq hl₀ hl₁ hzp)

private theorem abs_rpow_eq_sq_rpow_half (q x : ℝ) : |x| ^ q = (x ^ 2) ^ (q / 2) := by
  conv_lhs => rw [show q = 2 * (q / 2) by ring]
  rw [Real.rpow_mul (abs_nonneg x), Real.rpow_two, sq_abs]

/-- The concavity-of-variance upper bound for the far increment in G1 and G3. -/
theorem balancedFarIncrement_le_variance {q e : ℝ} (hq₀ : 0 ≤ q) (hq₂ : q ≤ 2)
    (he : |e| ≤ 1) (Z s : ℝ) :
    balancedFarIncrement q e Z s ≤ (Z ^ 2 + (1 - e ^ 2) * s ^ 2) ^ (q / 2) - |Z| ^ q := by
  obtain ⟨hel, heu⟩ := abs_le.mp he
  let a := (1 - e) / 2
  let b := (1 + e) / 2
  let X := Z - (1 + e) * s
  let Y := Z + (1 - e) * s
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hvariance : a * X ^ 2 + b * Y ^ 2 = Z ^ 2 + (1 - e ^ 2) * s ^ 2 := by
    dsimp [a, b, X, Y]
    ring
  have hconcave := (Real.concaveOn_rpow (show 0 ≤ q / 2 by linarith)
    (show q / 2 ≤ 1 by linarith)).2 (Set.mem_Ici.mpr (sq_nonneg X))
    (Set.mem_Ici.mpr (sq_nonneg Y)) ha hb hab
  simp only [smul_eq_mul, hvariance, ← abs_rpow_eq_sq_rpow_half] at hconcave
  exact sub_le_sub_right hconcave _

private theorem varianceFactor_nonneg {e : ℝ} (he : |e| ≤ 1) : 0 ≤ 1 - e ^ 2 := by
  obtain ⟨hel, heu⟩ := abs_le.mp he
  nlinarith only [mul_nonneg (show 0 ≤ 1 + e by linarith) (sub_nonneg.mpr heu)]

/-- The uniform q-power estimate, also valid at a zero far centre. -/
theorem balancedFarIncrement_le_power {q e : ℝ} (hq₀ : 0 ≤ q) (hq₂ : q ≤ 2)
    (he : |e| ≤ 1) (Z s : ℝ) :
    balancedFarIncrement q e Z s ≤ (1 - e ^ 2) ^ (q / 2) * |s| ^ q := by
  have hvar := varianceFactor_nonneg he
  have h := Real.rpow_add_le_add_rpow (sq_nonneg Z) (mul_nonneg hvar (sq_nonneg s))
    (show 0 ≤ q / 2 by linarith) (show q / 2 ≤ 1 by linarith)
  rw [Real.mul_rpow hvar (sq_nonneg s), ← abs_rpow_eq_sq_rpow_half,
    ← abs_rpow_eq_sq_rpow_half] at h
  exact (balancedFarIncrement_le_variance hq₀ hq₂ he Z s).trans ((sub_le_iff_le_add).2
    (by simpa only [add_comm] using h))

/-- Away from zero far centre, the tangent bound is quadratic in the transverse row. -/
theorem balancedFarIncrement_le_quadratic {q e Z : ℝ} (hq₀ : 0 ≤ q) (hq₂ : q ≤ 2)
    (he : |e| ≤ 1) (hZ : Z ≠ 0) (s : ℝ) :
    balancedFarIncrement q e Z s ≤ (q / 2) * (1 - e ^ 2) * |Z| ^ (q - 2) * s ^ 2 := by
  have hvar := varianceFactor_nonneg he
  let v := (1 - e ^ 2) * s ^ 2
  have hv : 0 ≤ v := mul_nonneg hvar (sq_nonneg s)
  have hsq : 0 < Z ^ 2 := sq_pos_of_ne_zero hZ
  have hfrac : 0 ≤ v / Z ^ 2 := div_nonneg hv hsq.le
  have hbern := rpow_one_add_le_one_add_mul_self (show -1 ≤ v / Z ^ 2 by linarith)
    (show 0 ≤ q / 2 by linarith) (show q / 2 ≤ 1 by linarith)
  have hscaled := mul_le_mul_of_nonneg_left hbern (Real.rpow_nonneg hsq.le (q / 2))
  have hsum : Z ^ 2 * (1 + v / Z ^ 2) = Z ^ 2 + v := by
    field_simp [hZ]
  rw [← Real.mul_rpow hsq.le (show 0 ≤ 1 + v / Z ^ 2 by linarith), hsum,
    ← abs_rpow_eq_sq_rpow_half] at hscaled
  have hdiv : |Z| ^ q / Z ^ 2 = |Z| ^ (q - 2) := by
    rw [← sq_abs Z, ← Real.rpow_two, ← Real.rpow_sub (abs_pos.mpr hZ)]
  calc
    _ ≤ (Z ^ 2 + v) ^ (q / 2) - |Z| ^ q :=
      balancedFarIncrement_le_variance hq₀ hq₂ he Z s
    _ ≤ |Z| ^ q * (1 + q / 2 * (v / Z ^ 2)) - |Z| ^ q := sub_le_sub_right hscaled _
    _ = (q / 2) * v * (|Z| ^ q / Z ^ 2) := by ring
    _ = _ := by rw [hdiv]; dsimp [v]; ring

private theorem rpow_mul_pred {x q : ℝ} (hx : 0 ≤ x) (hq : 0 < q) :
    x ^ q = x * x ^ (q - 1) := by
  calc
    x ^ q = x ^ ((1 : ℝ) + (q - 1)) := by rw [show 1 + (q - 1) = q by ring]
    _ = _ := by
      rw [Real.rpow_add' hx (by linarith), Real.rpow_one]

/-- At zero far centre, the exact variance factor controls the absolute power. -/
theorem balancedFarIncrement_zeroCenter_le {q e : ℝ} (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2)
    (he : |e| ≤ 1) (s : ℝ) :
    balancedFarIncrement q e 0 s ≤ (1 - e ^ 2) * |s| ^ q := by
  obtain ⟨hel, heu⟩ := abs_le.mp he
  have hleft : 0 ≤ 1 + e := by linarith
  have hright : 0 ≤ 1 - e := by linarith
  have hq : 0 < q := zero_lt_one.trans_le hq₁
  have hJ := (Real.concaveOn_rpow (show 0 ≤ q - 1 by linarith)
    (show q - 1 ≤ 1 by linarith)).2
    (Set.mem_Ici.mpr hleft) (Set.mem_Ici.mpr hright)
    (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : 0 ≤ (1/2 : ℝ))
    (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  simp only [smul_eq_mul, show (1/2 : ℝ) * (1 + e) + 1/2 * (1 - e) = 1 by ring,
    Real.one_rpow] at hJ
  have hJ' : ((1 + e) ^ (q - 1) + (1 - e) ^ (q - 1)) / 2 ≤ 1 := by linarith
  have hv := varianceFactor_nonneg he
  unfold balancedFarIncrement
  rw [zero_sub, zero_add, abs_neg, abs_mul, abs_mul, abs_of_nonneg hleft,
    abs_of_nonneg hright, Real.mul_rpow hleft (abs_nonneg s),
    Real.mul_rpow hright (abs_nonneg s), abs_zero, Real.zero_rpow hq.ne', sub_zero,
    rpow_mul_pred hleft hq, rpow_mul_pred hright hq]
  calc
    _ = ((1 - e ^ 2) * |s| ^ q) * (((1 + e) ^ (q - 1) + (1 - e) ^ (q - 1)) / 2) := by
      ring
    _ ≤ _ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hJ'
        (mul_nonneg hv (Real.rpow_nonneg (abs_nonneg s) q))

/-- A uniform gap bound for the pure transverse row, including negative imbalance. -/
theorem balancedFacetGap_transverse_bound {q μ l e : ℝ} (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2)
    (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1) (he : |e| ≤ 1) (s : ℝ) :
    ((1 - 3 * μ) * (1 - |e|) + μ * l) * |s| ^ q ≤ balancedFacetGap q μ l e 0 s 0 := by
  have hq : 0 < q := zero_lt_one.trans_le hq₁
  have hEven (u : ℝ) : balancedEvenGap q 0 u = |u| ^ q := by
    simp [balancedEvenGap, Real.zero_rpow hq.ne']
  have hJ : balancedJensenGap q l 0 0 = 0 := by
    simp [balancedJensenGap, balancedFarCenter, Real.zero_rpow hq.ne']
  have hZ : balancedFarCenter l l 0 0 = 0 := by simp [balancedFarCenter]
  have hv : balancedNearShift l e l 0 s 0 = e * s := by simp [balancedNearShift]
  have hf := balancedFarIncrement_zeroCenter_le hq₁ hq₂ he s
  have hVar : 1 - e ^ 2 ≤ 2 * (1 - |e|) := by
    nlinarith only [sq_nonneg (1 - |e|), sq_abs e]
  have hs : 0 ≤ |s| ^ q := Real.rpow_nonneg (abs_nonneg s) q
  have hfar := mul_le_mul_of_nonneg_left (hf.trans (mul_le_mul_of_nonneg_right hVar hs)) hμ₀
  have hnear := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_le_one (abs_nonneg e) he hq₁) hs)
    (sub_nonneg.mpr hμ₁)
  unfold balancedFacetGap
  rw [hJ, hZ, hv, hEven, hEven, abs_mul, Real.mul_rpow (abs_nonneg e) (abs_nonneg s)]
  nlinarith only [hfar, hnear]

/-- On the pure transverse axis the gap is positive away from the zero row. -/
theorem balancedFacetGap_transverse_pos {q μ l e s : ℝ} (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2)
    (hμ₀ : 0 ≤ μ) (hμ₁ : μ < 1/3) (hl : 0 ≤ l) (he : |e| < 1) (hs : s ≠ 0) :
    0 < balancedFacetGap q μ l e 0 s 0 := by
  have hcoef : 0 < (1 - 3 * μ) * (1 - |e|) + μ * l :=
    add_pos_of_pos_of_nonneg (mul_pos (by linarith) (sub_pos.mpr he)) (mul_nonneg hμ₀ hl)
  exact (mul_pos hcoef (Real.rpow_pos_of_pos (abs_pos.mpr hs) q)).trans_le
    (balancedFacetGap_transverse_bound hq₁ hq₂ hμ₀ (by linarith) he.le s)

private theorem continuous_transverse_chart {q : ℝ} (hq : 0 ≤ q) (μ l e s : ℝ) :
    Continuous (fun x : ℝ × ℝ => balancedFacetGap q μ l e x.1 s x.2) := by
  let f (x : ℝ) := |x| ^ q
  have hf : Continuous f := (Real.continuous_rpow_const hq).comp continuous_abs
  have hEven {u v : ℝ × ℝ → ℝ} (hu : Continuous u) (hv : Continuous v) :
      Continuous (fun x => balancedEvenGap q (u x) (v x)) :=
    (((hf.comp (hu.add hv)).add (hf.comp (hu.sub hv))).div_const 2).sub (hf.comp hu)
  have hZ : Continuous (fun x : ℝ × ℝ => balancedFarCenter l l x.1 x.2) :=
    (continuous_const.mul continuous_snd).add (continuous_const.mul continuous_fst)
  have hV : Continuous (fun x : ℝ × ℝ => balancedNearShift l e l x.1 s x.2) :=
    (continuous_const.add (continuous_const.mul continuous_snd)).sub
      (continuous_const.mul continuous_fst)
  have hJ : Continuous (fun x : ℝ × ℝ => balancedJensenGap q l x.1 x.2) :=
    ((continuous_const.mul (hf.comp continuous_snd)).add
      (continuous_const.mul (hf.comp continuous_fst))).sub (hf.comp hZ)
  have hH : Continuous (fun x : ℝ × ℝ => balancedFarIncrement q e
      (balancedFarCenter l l x.1 x.2) s) :=
    ((continuous_const.mul (hf.comp (hZ.sub continuous_const))).add
      (continuous_const.mul (hf.comp (hZ.add continuous_const)))).sub (hf.comp hZ)
  exact (((continuous_const.mul hJ).add
    (continuous_const.mul (hEven continuous_fst continuous_const))).sub
    (continuous_const.mul (hEven continuous_fst hV))).sub (continuous_const.mul hH)

private theorem positive_on_rectangle {G : ℝ × ℝ → ℝ} (hG : Continuous G)
    (hG₀ : 0 < G (0, 0)) : ∃ δ : ℝ, 0 < δ ∧ ∀ p z : ℝ, |p| < δ → |z| < δ →
      0 < G (p, z) := by
  have hopen : IsOpen {x : ℝ × ℝ | 0 < G x} := isOpen_lt continuous_const hG
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen (0, 0) hG₀
  refine ⟨δ, hδ, fun p z hp hz => ?_⟩
  have hdist : dist (p, z) ((0 : ℝ), (0 : ℝ)) < δ := by
    rw [Prod.dist_eq]
    change max (dist p 0) (dist z 0) < δ
    simpa only [Real.dist_eq, sub_zero, max_lt_iff] using And.intro hp hz
  exact hball (Metric.mem_ball.mpr hdist)

/-- At fixed nonzero transverse coordinate the strict gap extends to a neighbourhood
in the two other coordinates. -/
theorem balancedFacetGap_transverse_open {q μ l e s : ℝ} (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2)
    (hμ₀ : 0 ≤ μ) (hμ₁ : μ < 1/3) (hl : 0 ≤ l) (he : |e| < 1) (hs : s ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p z : ℝ, |p| < δ → |z| < δ →
      0 < balancedFacetGap q μ l e p s z :=
  positive_on_rectangle (continuous_transverse_chart (zero_le_one.trans hq₁) μ l e s)
    (balancedFacetGap_transverse_pos hq₁ hq₂ hμ₀ hμ₁ hl he hs)

end HlawkaSchatten.BelowExponent
