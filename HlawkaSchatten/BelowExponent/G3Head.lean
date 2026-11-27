/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3Cone
public import HlawkaSchatten.BelowExponent.BulkGeometry
import all HlawkaSchatten.BelowExponent.G3
import all HlawkaSchatten.BelowExponent.G3Cone
import all HlawkaSchatten.BelowExponent.G1Compact
import all HlawkaSchatten.BelowExponent.G1Far
import all HlawkaSchatten.BelowExponent.G1Large
import all HlawkaSchatten.BelowExponent.G1

/-! Estimates for the normalized z=1 chart of the G3 vertex corner. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set

open private g3_k_max from HlawkaSchatten.BelowExponent.G3
open private adjustedPower_first_deriv adjustedPower_second_deriv adjustedPower_continuous
  from HlawkaSchatten.BelowExponent.G3Cone
open private g1Curvature g1Curvature_nonneg g1_evenGap_abs_bounds from HlawkaSchatten.BelowExponent.G1Compact
open private criticalQ_lo criticalQ_hi evenGap_scale from HlawkaSchatten.BelowExponent.G1Far
open private evenGap_shrink evenGap_large_lower evenGap_neg_center evenGap_neg_shift absPower_deriv from HlawkaSchatten.BelowExponent.G1Large
open private evenGap_nonneg evenGap_convex absPower_convex half_pow_q from HlawkaSchatten.BelowExponent.G1

private theorem head_q_lo : 19/12 ≤ criticalQ :=
  (by norm_num : (19/12:ℝ) ≤ 1054/665).trans criticalQ_lo

private theorem head_q_hi : criticalQ ≤ 65/41 :=
  criticalQ_bracket.2.le.trans (by norm_num)

private theorem head_q_pos : 1 < criticalQ := (by norm_num : (1:ℝ) < 19/12).trans_le head_q_lo

private theorem head_curvature_upper : g1Curvature ≤ 93/200 := by
  have hm := mul_le_mul head_q_hi (sub_le_sub_right head_q_hi 1)
    (sub_nonneg.mpr head_q_pos.le) (by norm_num : (0:ℝ) ≤ 65/41)
  unfold g1Curvature
  linarith only [hm]

private theorem head_curvature_lower : 27/64 ≤ g1Curvature := by
  have hm := mul_le_mul head_q_lo (sub_le_sub_right head_q_lo 1)
    (by norm_num : (0:ℝ) ≤ 19/12-1) (zero_le_one.trans head_q_pos.le)
  unfold g1Curvature
  linarith only [hm]

private theorem head_adjusted_concave {m c : ℝ} (hm : 0 < m)
    (hc : g1Curvature*m^(criticalQ-2) ≤ c) :
    ConcaveOn ℝ (Ici m) (fun x => x^criticalQ-c*x^2) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos
    (f' := fun x => criticalQ*x^(criticalQ-1)-2*c*x)
    (f'' := fun x => 2*g1Curvature*x^(criticalQ-2)-2*c)
    (convex_Ici _) (adjustedPower_continuous c).continuousOn ?_ ?_ ?_
  · intro x hx
    rw [interior_Ici] at hx
    exact (adjustedPower_first_deriv c (hm.trans hx)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (adjustedPower_second_deriv c (hm.trans hx)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hp := Real.rpow_le_rpow_of_nonpos hm hx.le
      (sub_nonpos.mpr (head_q_hi.trans (by norm_num) : criticalQ ≤ 2))
    have hn := mul_le_mul_of_nonneg_left hp g1Curvature_nonneg
    linarith only [hn,hc]

private theorem head_center_bounds {h k p : ℝ} (hh : 0 < h) (hh₁ : h ≤ 17/32)
    (hk : 0 < k) (hk₁ : k ≤ 1/9) (hp : |p| ≤ 1/8) :
    11/12 ≤ balancedFarCenter (h*k) (h*k) p 1 ∧ balancedFarCenter (h*k) (h*k) p 1 < 1 := by
  have hW : 0 < 1-p := by linarith only [(abs_le.mp hp).2]
  have hm := mul_le_mul (mul_le_mul hh₁ hk₁ hk.le (by norm_num : (0:ℝ) ≤ 17/32))
    (show 1-p ≤ 9/8 by linarith only [(abs_le.mp hp).1]) hW.le (by norm_num)
  have hPos := mul_pos (mul_pos hh hk) hW
  unfold balancedFarCenter
  constructor <;> linarith only [hm,hPos]

private theorem head_jensen_bound {l p : ℝ} (hl : 0 < l) (hZ₀ : 11/12 ≤ balancedFarCenter l l p 1)
    (hZ₁ : balancedFarCenter l l p 1 < 1) :
    |p|^criticalQ-1+criticalQ*(1-p)-(1/2)*l*(1-p)^2 ≤
      balancedJensenGap criticalQ l p 1/l := by
  let Z := balancedFarCenter l l p 1
  have h₀ : (9/10:ℝ)^(criticalQ-2) ≤ 16/15 := by
    have hpow : (10/9:ℝ)^(1/2:ℝ) ≤ 16/15 := by
      simpa only [Nat.cast_one, Nat.cast_ofNat] using
        (natRat_rpow_le_iff (a := 10) (c := 16) (m := 1) (n := 2)
          (by decide : 0 < (9:ℕ)) (by decide : 0 < (15:ℕ)) (by decide)).mpr (by decide)
    have heq : (9/10:ℝ)^(-(1/2):ℝ) = (10/9:ℝ)^(1/2:ℝ) := by
      rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num : (0:ℝ) ≤ 9/10)]
      norm_num
    exact (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
      (show -(1/2:ℝ) ≤ criticalQ-2 by linarith [head_q_lo])).trans (heq ▸ hpow)
  have hc : g1Curvature*(9/10:ℝ)^(criticalQ-2) ≤ 1/2 := by
    have hh := mul_le_mul head_curvature_upper h₀ (by positivity) (by norm_num : (0:ℝ) ≤ 93/200)
    linarith only [hh]
  have hC := head_adjusted_concave (by norm_num : (0:ℝ) < 9/10) hc
  have hT := hC.le_slope_of_hasDerivAt
    (mem_Ici.mpr (show (9/10:ℝ) ≤ Z by linarith only [hZ₀]))
    (mem_Ici.mpr (by norm_num : (9/10:ℝ) ≤ 1)) hZ₁
    (adjustedPower_first_deriv (1/2) (by norm_num : (0:ℝ) < 1))
  simp only [slope_def_field, Real.one_rpow, one_pow, mul_one] at hT
  have h' := (le_div_iff₀ (sub_pos.mpr hZ₁)).mp hT
  have hEq : 1-Z = l*(1-p) := by dsimp [Z,balancedFarCenter]; ring
  apply (le_div_iff₀ hl).2
  unfold balancedJensenGap
  change _ ≤ (1-l)*|(1:ℝ)|^criticalQ+l*|p|^criticalQ-|Z|^criticalQ
  rw [abs_one, Real.one_rpow, abs_of_pos (by linarith only [hZ₀] : 0 < Z)]
  nlinarith only [h', congrArg (fun x : ℝ => x^2) hEq,
    congrArg (fun x => criticalQ*x) hEq]

private theorem head_far_bound {h Z s : ℝ} (hh : 0 < h) (hh₁ : h ≤ 17/32)
    (hZ : 11/12 ≤ Z) (hs : |s| ≤ 1/8) :
    balancedFarIncrement criticalQ (1-h) Z s/h ≤ (9/8)*s^2 := by
  let a := h/2
  let b := 1-h/2
  let X := Z-(2-h)*s
  let Y := Z+h*s
  have hp : (2/3:ℝ)^(criticalQ-2) ≤ 6/5 := by
    have hb : (3/2:ℝ)^(5/12:ℝ) ≤ 6/5 := by
      simpa only [Nat.cast_ofNat] using
        (natRat_rpow_le_iff (a := 3) (c := 6) (m := 5) (n := 12)
          (by decide : 0 < (2:ℕ)) (by decide : 0 < (5:ℕ)) (by decide)).mpr (by decide)
    have heq : (2/3:ℝ)^(-(5/12):ℝ) = (3/2:ℝ)^(5/12:ℝ) := by
      rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2/3)]
      norm_num
    exact (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
      (show -(5/12:ℝ) ≤ criticalQ-2 by linarith only [head_q_lo])).trans (heq ▸ hb)
  have hc : g1Curvature*(2/3:ℝ)^(criticalQ-2) ≤ 9/16 := by
    have h := mul_le_mul head_curvature_upper hp (by positivity) (by norm_num : (0:ℝ) ≤ 93/200)
    linarith only [h]
  have hC := head_adjusted_concave (by norm_num : (0:ℝ) < 2/3) hc
  have hX : 2/3 ≤ X := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp hs).2 (show 0 ≤ 2-h by linarith)
    dsimp [X]
    linarith only [h,hh.le,hZ]
  have hY : 2/3 ≤ Y := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp hs).1 hh.le
    dsimp [Y]
    linarith only [h,hh₁,hZ]
  have hab : a+b=1 := by dsimp [a,b]; ring
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hmean : a*X+b*Y=Z := by dsimp [a,b,X,Y]; ring
  have hvar : a*X^2+b*Y^2-Z^2=h*(2-h)*s^2 := by dsimp [a,b,X,Y]; ring
  have hj := hC.2 (mem_Ici.mpr hX) (mem_Ici.mpr hY) ha hb hab
  simp only [smul_eq_mul,hmean] at hj
  apply (div_le_iff₀ hh).2
  unfold balancedFarIncrement
  rw [show (1-(1-h))/2=a by dsimp [a]; ring,
    show (1+(1-h))/2=b by dsimp [b]; ring,
    show Z-(1+(1-h))*s=X by dsimp [X]; ring,
    show Z+(1-(1-h))*s=Y by dsimp [Y]; ring,
    abs_of_nonneg (by linarith only [hX] : 0 ≤ X), abs_of_nonneg (by linarith only [hY] : 0 ≤ Y),
    abs_of_nonneg (by linarith only [hZ] : 0 ≤ Z)]
  linarith only [hj,hvar,mul_nonneg (mul_nonneg hh.le hh.le) (sq_nonneg s)]

private theorem head_eighth_power : (1/8:ℝ)^(criticalQ-2) = 64/27 := by
  have h : (1/8:ℝ)^criticalQ = 1/27 := by
    rw [show (1/8:ℝ) = (1/2:ℝ) ^ (3:ℝ) by rw [Real.rpow_ofNat]; norm_num,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2), mul_comm (3:ℝ),
      Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    rw [show (1/2:ℝ)^criticalQ=1/3 by
      rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 2),
        Real.one_rpow,two_rpow_criticalQ],
      Real.rpow_ofNat]
    norm_num
  rw [Real.rpow_sub (by norm_num : (0:ℝ) < 1/8), h, Real.rpow_two]
  norm_num

private theorem head_small_evenGap {p s : ℝ} (hp : |p| ≤ 1/8) (hs : |s| ≤ 1/8) :
    s^2 ≤ balancedEvenGap criticalQ p s := by
  by_cases h : |p| ≤ |s|
  · obtain h₀ | h₀ := (abs_nonneg s).eq_or_lt
    · have hz : s = 0 := abs_eq_zero.mp h₀.symm
      simpa [hz] using evenGap_nonneg head_q_pos.le p s
    have hP := Real.rpow_le_rpow_of_nonpos h₀ hs (sub_nonpos.mpr (head_q_hi.trans (by norm_num) : criticalQ ≤ 2))
    rw [head_eighth_power,Real.rpow_sub h₀,Real.rpow_two] at hP
    have hsquare := (le_div_iff₀ (sq_pos_of_pos h₀)).mp hP
    rw [sq_abs] at hsquare
    linarith only [evenGap_large_lower h,hsquare,sq_nonneg s]
  · have hP : 0 < |p| := (abs_nonneg s).trans_lt (lt_of_not_ge h)
    have hS : |s / (|p|)| ≤ 1 := by
      rw [abs_div, abs_abs]
      exact (div_le_one₀ hP).mpr (le_of_not_ge h)
    have hh := (g1_evenGap_abs_bounds hS).1
    have hq := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (abs_nonneg p) criticalQ)
    have hh' := evenGap_scale (q := criticalQ) (abs_nonneg p) 1 (s/|p|)
    rw [mul_one,mul_div_cancel₀ _ hP.ne'] at hh'
    rw [← hh'] at hq
    have hp' : balancedEvenGap criticalQ |p| s = balancedEvenGap criticalQ p s := by
      rcases le_or_gt 0 p with hx | hx
      · rw [abs_of_nonneg hx]
      · rw [abs_of_neg hx,evenGap_neg_center]
    rw [hp'] at hq
    have hco := Real.rpow_le_rpow_of_nonpos hP hp (sub_nonpos.mpr (head_q_hi.trans (by norm_num) : criticalQ ≤ 2))
    rw [head_eighth_power] at hco
    have hcoef : 1 ≤ g1Curvature*|p|^(criticalQ-2) := by
      have h := mul_le_mul head_curvature_lower hco (by norm_num) g1Curvature_nonneg
      linarith only [h]
    have heq : |p|^criticalQ*(g1Curvature*(s/|p|)^2) = (g1Curvature*|p|^(criticalQ-2))*s^2 := by
      rw [Real.rpow_sub hP, Real.rpow_two]
      ring
    rw [heq] at hq
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg s)
    rw [one_mul] at h
    exact h.trans hq

private theorem head_weight_upper {h σ : ℝ} (hh₀ : 0 ≤ h) (hh₁ : h ≤ 1)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1/5) : g3Weight h σ ≤ 3/10 := by
  have hpow : σ^(12/25:ℝ) ≤ 37/80 := by
    have hc : (1/5:ℝ)^(12/25:ℝ) ≤ 37/80 := by
      simpa only [Nat.cast_one, Nat.cast_ofNat] using
        (natRat_rpow_le_iff (a:=1) (c:=37) (m:=12) (n:=25)
          (by decide : 0<(5:ℕ)) (by decide : 0<(80:ℕ)) (by decide)).mpr (by decide)
    exact (Real.rpow_le_rpow hσ₀ hσ₁ (by norm_num)).trans hc
  have hf : (if σ < 3/20 then (1:ℝ) else 49/50) ≤ 1 := by split <;> norm_num
  unfold g3Weight
  calc
    _ ≤ (1:ℝ)*(3/5)*(17/16)*(37/80) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hf (by norm_num))
        (by linarith) (by positivity) (by norm_num)) hpow (by positivity) (by norm_num)
    _ ≤ 3/10 := by norm_num

private theorem head_jensen_third {h k p : ℝ} (hh : 0<h) (hh₁ : h≤17/32)
    (hk : 0<k) (hk₁ : k≤1/9) (hp : |p|≤1/8) :
    1/3 ≤ balancedJensenGap criticalQ (h*k) p 1/(h*k) := by
  obtain ⟨hZ₀,hZ₁⟩ := head_center_bounds hh hh₁ hk hk₁ hp
  have hw : (7/8:ℝ) ≤ 1-p := by linarith only [(abs_le.mp hp).2]
  have hw' : 1-p ≤ (9/8:ℝ) := by linarith only [(abs_le.mp hp).1]
  have hW : 0 ≤ 1-p := (by norm_num : (0:ℝ)≤7/8).trans hw
  have hProd := mul_le_mul head_q_lo hw (by norm_num) (zero_le_one.trans head_q_pos.le)
  have hCost := mul_le_mul (mul_le_mul hh₁ hk₁ hk.le (by norm_num : (0:ℝ)≤17/32))
    (pow_le_pow_left₀ hW hw' 2) (sq_nonneg _) (by norm_num)
  have hJ := head_jensen_bound (mul_pos hh hk) hZ₀ hZ₁
  linarith only [hJ,hProd,hCost,Real.rpow_nonneg (abs_nonneg p) criticalQ]

private theorem head_gap_div_h {h σ p s : ℝ} (hh : h ≠ 0) (hk : σ/(2-σ) ≠ 0) :
    let k := σ/(2-σ)
    let μ := g3Weight h σ
    let u := k*(1-p)
    let A := balancedEvenGap criticalQ p
    g3FacetGap h σ p s 1/h =
      μ*k*(balancedJensenGap criticalQ (h*k) p 1/(h*k)+A s) +
      (1-μ)*((A s-A ((1-h)*s+h*u))/h) -
      μ*(balancedFarIncrement criticalQ (1-h) (balancedFarCenter (h*k) (h*k) p 1) s/h) := by
  dsimp only [g3FacetGap]
  rw [balancedFacetGap_div_h _ _ _ _ _ _ _ hh hk, balancedNearShift_facet]
  rw [show h*(σ/(2-σ))*(1-p) = h*((σ/(2-σ))*(1-p)) by ring]
  ring

private theorem head_outside_middle {h σ p s : ℝ} (hh : 0<h) (hσ : 0<σ) (hσ₁ : σ≤1/5)
    (hh₁ : h≤1/(2-σ/(2-σ))) (hp : |p|≤1/8) (hs : |s|≤1/8)
    (hout : s ≤ -(σ/(2-σ)*(1-p))/2 ∨ σ/(2-σ)*(1-p) ≤ s) :
    0 ≤ g3FacetGap h σ p s 1 := by
  let k := σ/(2-σ)
  let μ := g3Weight h σ
  let b := 1-μ
  let u := k*(1-p)
  let v := (1-h)*s+h*u
  let A := balancedEvenGap criticalQ p
  let J := balancedJensenGap criticalQ (h*k) p 1/(h*k)
  let H := balancedFarIncrement criticalQ (1-h) (balancedFarCenter (h*k) (h*k) p 1) s/h
  have hhM : h ≤ 17/32 := (g3_h_max hσ₁ hh₁).trans (by norm_num)
  have hh' : h ≤ 1 := hhM.trans (by norm_num)
  have hk : 0<k := div_pos hσ (by linarith)
  have hkM : k ≤ 1/9 := g3_k_max hσ₁
  have hu : 0<u := mul_pos hk (by linarith only [(abs_le.mp hp).2])
  have hμ : 0<μ := (g3_weight_pos_lt_third hh.le hh' hσ hσ₁).1
  have hμM : μ≤3/10 := head_weight_upper hh.le hh' hσ.le hσ₁
  have hb : 0≤b := by dsimp [b]; linarith only [hμM]
  have hA : s^2 ≤ A s := head_small_evenGap hp hs
  have hA₀ : 0 ≤ A s := (sq_nonneg _).trans hA
  have hJ : 1/3≤J := head_jensen_third hh hhM hk hkM hp
  have hH : H≤(9/8)*s^2 := head_far_bound hh hhM (head_center_bounds hh hhM hk hkM hp).1 hs
  have hv : |v| ≤ (1-h)*|s|+h*u := by
    dsimp [v]
    calc
      _ ≤ |(1-h)*s|+|h*u| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hh'), abs_of_nonneg hh.le,
        abs_of_pos hu]
  suffices hg : 0 ≤ g3FacetGap h σ p s 1/h by
    simpa only [zero_mul] using (le_div_iff₀ hh).mp hg
  rw [head_gap_div_h hh.ne' hk.ne']
  change 0 ≤ μ*k*(J+A s)+b*((A s-A v)/h)-μ*H
  have hμk : 0 ≤ μ*k := mul_nonneg hμ.le hk.le
  by_cases hfar : 2*u≤|s|
  · have hR₀ : 0≤1-h/2 := by linarith
    have hR₁ : 1-h/2≤1 := by linarith
    have hv' : |v|≤(1-h/2)*|s| := hv.trans (by
      have h := mul_le_mul_of_nonneg_left hfar hh.le
      linarith only [h])
    have hsr := evenGap_shrink (p:=p) head_q_pos (head_q_hi.trans (by norm_num)) hR₁ hR₀ hv'
    have hpw : (1-h/2)^criticalQ ≤ 1-h/2 := by
      exact Real.rpow_le_self_of_le_one hR₀ hR₁ head_q_pos.le
    have hN : (1/2)*A s ≤ (A s-A v)/h := by
      apply (le_div_iff₀ hh).2
      linarith only [hsr.trans (mul_le_mul_of_nonneg_right hpw hA₀)]
    have hC : (9/8)*μ ≤ b/2 := by dsimp [b]; linarith only [hμM]
    have hB := mul_le_mul_of_nonneg_right hC (sq_nonneg s)
    have hT := mul_le_mul_of_nonneg_left hA (by linarith : 0≤b/2)
    have hJ₀ : 0≤μ*k*(J+A s) := mul_nonneg hμk (by linarith)
    linarith only [hJ₀,hB,hT,mul_le_mul_of_nonneg_left hN hb,mul_le_mul_of_nonneg_left hH hμ.le]
  · have hv' : |v| ≤ |s| := by
      rcases hout with hneg | hpos
      · change s≤-u/2 at hneg
        have hsneg : s<0 := by linarith only [hneg,hu]
        rw [abs_of_neg hsneg]
        refine abs_le.mpr ⟨?_,?_⟩
        · dsimp [v]; nlinarith only [mul_nonneg hh.le hu.le,mul_nonneg hh.le (neg_nonneg.mpr hsneg.le)]
        · have he : h≤2/3 := hhM.trans (by norm_num)
          have h₁ := mul_le_mul_of_nonneg_left (show u≤2*(-s) by linarith only [hneg]) hh.le
          have h₂ := mul_le_mul_of_nonneg_right he (show 0≤-s by linarith)
          dsimp [v]
          nlinarith only [h₁,h₂]
      · change u≤s at hpos
        have h := mul_le_mul_of_nonneg_left hpos hh.le
        rw [abs_of_pos (hu.trans_le hpos)] at hv ⊢
        linarith only [hv,h]
    have hN : 0≤(A s-A v)/h := by
      apply div_nonneg _ hh.le
      have hh := evenGap_shrink (p:=p) head_q_pos (head_q_hi.trans (by norm_num)) (R:=1) le_rfl zero_le_one
        (by simpa only [one_mul] using hv')
      simpa only [Real.one_rpow,one_mul] using sub_nonneg.mpr hh
    have hLs := mul_le_mul_of_nonneg_right (le_of_not_ge hfar) (abs_nonneg s)
    rw [← pow_two, sq_abs] at hLs
    have hUs := mul_le_mul_of_nonneg_left hs hu.le
    have hpw := mul_le_mul_of_nonneg_left (show 1-p≤9/8 by linarith only [(abs_le.mp hp).1]) hk.le
    have hkJ : H≤k*J := by
      have hcost := mul_le_mul_of_nonneg_left hJ hk.le
      dsimp [u] at hUs
      linarith only [hH,hLs,hUs,hpw,hcost,hk.le]
    have hJcost := mul_le_mul_of_nonneg_left hkJ hμ.le
    linarith only [hJcost,mul_nonneg hb hN,mul_nonneg hμk hA₀]

private theorem blend_power_ge {A B C D r : ℝ}
    (hA : 0≤A) (hB₀ : A≤B) (hB₁ : B≤D) (hsum : B+C=A+D) (hr₀ : 0≤r) (hr₁ : r≤1) :
    A^r+D^r ≤ B^r+C^r := by
  obtain ⟨w,hw,hB⟩ := exists_interval_lerp hB₀ hB₁
  have hC : C = w*A+(1-w)*D := by linarith only [hsum,hB]
  have hc := Real.concaveOn_rpow hr₀ hr₁
  have hd : 0≤D := hA.trans (hB₀.trans hB₁)
  have h₁ := hc.2 (mem_Ici.mpr hA) (mem_Ici.mpr hd) (sub_nonneg.mpr hw.2) hw.1
    (by ring : 1-w+w=1)
  have h₂ := hc.2 (mem_Ici.mpr hA) (mem_Ici.mpr hd) hw.1 (sub_nonneg.mpr hw.2)
    (by ring : w+(1-w)=1)
  simp only [smul_eq_mul, ← hB, ← hC] at h₁ h₂
  linarith only [h₁,h₂]

private noncomputable def signedPower (r x : ℝ) : ℝ := if 0≤x then |x|^r else -|x|^r

private theorem signedPower_even_sum {r P x y : ℝ} (hr : 0<r) (hr₁ : r≤1)
    (hP : 0≤P) (hx : 0≤x) (hxy : x≤y) :
    signedPower r (P+y)+signedPower r (P-y) ≤ signedPower r (P+x)+signedPower r (P-x) := by
  have hval (z : ℝ) (hz : 0≤z) : signedPower r z = z^r := by simp [signedPower,hz,abs_of_nonneg]
  have hneg (z : ℝ) (hz : 0≤z) : signedPower r (-z) = -z^r := by
    rcases hz.eq_or_lt with he | he
    · subst z
      simp [signedPower,Real.zero_rpow hr.ne']
    · simp [signedPower,show ¬0≤-z by linarith,abs_of_pos he]
  have hLow {x y : ℝ} (hx : 0≤x) (hxy : x≤y) (hY : y≤P) :
      signedPower r (P+y)+signedPower r (P-y) ≤ signedPower r (P+x)+signedPower r (P-x) := by
    rw [hval _ (by linarith),hval _ (by linarith),hval _ (by linarith),hval _ (by linarith)]
    have h := blend_power_ge (A:=P-y) (B:=P+x) (C:=P-x) (D:=P+y)
      (by linarith) (by linarith) (by linarith) (by ring) hr.le hr₁
    linarith only [h]
  have hHigh {x y : ℝ} (hx : P≤x) (hxy : x≤y) :
      signedPower r (P+y)+signedPower r (P-y) ≤ signedPower r (P+x)+signedPower r (P-x) := by
    rw [hval (P+y) (by linarith),hval (P+x) (by linarith),show P-y=-(y-P) by ring,
      show P-x=-(x-P) by ring,hneg _ (by linarith),hneg _ (by linarith)]
    have h := blend_power_ge (A:=x-P) (B:=P+x) (C:=y-P) (D:=P+y)
      (by linarith) (by linarith) (by linarith) (by ring) hr.le hr₁
    linarith only [h]
  by_cases hy : y≤P
  · exact hLow hx hxy hy
  by_cases hx' : P≤x
  · exact hHigh hx' hxy
  exact (hHigh le_rfl (le_of_not_ge hy)).trans (hLow hx (le_of_not_ge hx') le_rfl)

private theorem evenGap_difference_antitone {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    AntitoneOn (fun p => balancedEvenGap criticalQ p y-balancedEvenGap criticalQ p x) (Ici 0) := by
  let q := criticalQ
  let D := signedPower (q-1)
  have hDer (p : ℝ) : HasDerivAt (fun p => balancedEvenGap q p y-balancedEvenGap q p x)
      (q*((D (p+y)+D (p-y))-(D (p+x)+D (p-x)))/2) p := by
    have h₁ (t : ℝ) := (absPower_deriv head_q_pos (p+t)).comp p ((hasDerivAt_id p).add_const t)
    have h₂ (t : ℝ) := (absPower_deriv head_q_pos (p-t)).comp p ((hasDerivAt_id p).sub_const t)
    have hd (t : ℝ) : HasDerivAt (fun p => balancedEvenGap q p t)
        ((q*D (p+t)+q*D (p-t))/2-q*D p) p := by
      have hh := (((h₁ t).add (h₂ t)).div_const 2).sub (absPower_deriv head_q_pos p)
      convert! hh using 1
      simp [D,signedPower,q]
    convert! (hd y).sub (hd x) using 1
    ring
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun x _ => (hDer x).continuousAt.continuousWithinAt)
    (fun x _ => (hDer x).differentiableAt.differentiableWithinAt) ?_
  intro p hp
  rw [(hDer p).deriv]
  have hb : D (p+y)+D (p-y) ≤ D (p+x)+D (p-x) :=
    signedPower_even_sum (by dsimp [q]; linarith only [head_q_lo])
      (by dsimp [q]; linarith only [head_q_hi]) (interior_subset hp) hx hxy
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (zero_le_one.trans head_q_pos.le) (sub_nonpos.mpr hb))
    (by norm_num)

private theorem evenGap_abs_shift {p s : ℝ} :
    balancedEvenGap criticalQ p |s| = balancedEvenGap criticalQ p s := by
  rcases le_or_gt 0 s with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h,evenGap_neg_shift]

private theorem evenGap_abs_center {p s : ℝ} :
    balancedEvenGap criticalQ |p| s = balancedEvenGap criticalQ p s := by
  rcases le_or_gt 0 p with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h,evenGap_neg_center]

private theorem head_secant {h H u p s P : ℝ} (hh : 0<h) (hH : h≤H)
    (hu : 0<u) (hP : 0≤P) (hPu : P≤|p|/u) :
    (balancedEvenGap criticalQ p ((1-h)*s+h*u)-balancedEvenGap criticalQ p s)/h ≤
      u^criticalQ * max 0 ((balancedEvenGap criticalQ P ((1-H)*(s/u)+H)-
        balancedEvenGap criticalQ P (s/u))/H) := by
  let A := balancedEvenGap criticalQ p
  let v := (1-H)*s+H*u
  let r := h/H
  have hH₀ := hh.trans_le hH
  have hr₀ : 0≤r := div_nonneg hh.le hH₀.le
  have hr₁ : r≤1 := (div_le_one₀ hH₀).mpr hH
  have hr : r*H=h := by dsimp [r]; field_simp [hH₀.ne']
  have hc := (evenGap_convex head_q_pos.le p).2 (mem_univ s) (mem_univ v)
    (sub_nonneg.mpr hr₁) hr₀ (by ring : 1-r+r=1)
  simp only [smul_eq_mul] at hc
  have hblend : (1-r)*s+r*v=(1-h)*s+h*u := by dsimp [v]; linarith only [congrArg (fun x => x*(u-s)) hr]
  rw [hblend] at hc
  have hu' : 0≤u^criticalQ := Real.rpow_nonneg hu.le _
  have hD : (A ((1-h)*s+h*u)-A s)/h ≤ (A v-A s)/H := by
    apply (div_le_div_iff₀ hh hH₀).2
    have ht := mul_le_mul_of_nonneg_right hc hH₀.le
    linarith only [ht,congrArg (fun x => x*(A v-A s)) hr]
  refine hD.trans ?_
  let a := s/u
  let b := (1-H)*a+H
  let Q := |p|/u
  have hS (x : ℝ) : balancedEvenGap criticalQ p (u*x) =
      u^criticalQ*balancedEvenGap criticalQ Q x := by
    have hs := evenGap_scale (q:=criticalQ) hu.le Q x
    rw [show u*Q=|p| by dsimp [Q]; field_simp [hu.ne'],evenGap_abs_center] at hs
    exact hs
  have hsv : u*b=v := by dsimp [a,b,v]; field_simp [hu.ne']
  have hsa : u*a=s := by dsimp [a]; field_simp [hu.ne']
  change (A v-A s)/H ≤ u^criticalQ*max 0 ((balancedEvenGap criticalQ P b-balancedEvenGap criticalQ P a)/H)
  rw [show A v=u^criticalQ*balancedEvenGap criticalQ Q b by rw [← hsv]; exact hS b,
    show A s=u^criticalQ*balancedEvenGap criticalQ Q a by rw [← hsa]; exact hS a]
  rw [← mul_sub,mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hu'
  by_cases hab : |a|≤|b|
  · have hmono := evenGap_difference_antitone (abs_nonneg a) hab (mem_Ici.mpr hP)
      (mem_Ici.mpr (div_nonneg (abs_nonneg p) hu.le)) hPu
    simp only [evenGap_abs_shift] at hmono
    exact (div_le_div_of_nonneg_right hmono hH₀.le).trans (le_max_right _ _)
  · have hmono := evenGap_shrink (p:=Q) head_q_pos (head_q_hi.trans (by norm_num)) (R:=1) le_rfl zero_le_one
      (by simpa only [one_mul] using (le_of_not_ge hab : |b|≤|a|))
    simp only [Real.one_rpow,one_mul] at hmono
    exact (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hmono) hH₀.le).trans (le_max_left _ _)

private theorem one64_pow_criticalQ : (1/64:ℝ)^criticalQ = 1/729 := by
  rw [show (1/64:ℝ) = (1/2:ℝ)^(6:ℝ) by rw [Real.rpow_ofNat]; norm_num,
    ← Real.rpow_mul (by norm_num : (0:ℝ)≤1/2), mul_comm (6:ℝ),
    Real.rpow_mul (by norm_num : (0:ℝ)≤1/2),half_pow_q,Real.rpow_ofNat]
  norm_num

private theorem weighted_power_error {x y w : ℝ} (hw : w∈Icc 0 1) (hxy : |y-x|≤1/32) :
    (1-w)*|x|^criticalQ+w*|y|^criticalQ-|((1-w)*x+w*y)|^criticalQ ≤ 1/729 := by
  let e := 2*w-1
  let z := (1-w)*x+w*y
  let s := (y-x)/2
  have he : |e|≤1 := abs_le.mpr ⟨by dsimp [e]; linarith [hw.1],by dsimp [e]; linarith [hw.2]⟩
  have hs : |s|≤1/64 := by
    dsimp [s]
    rw [abs_div,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    linarith only [hxy]
  have hq₀ := zero_le_one.trans head_q_pos.le
  have h := balancedFarIncrement_le_power hq₀ (head_q_hi.trans (by norm_num)) he z s
  unfold balancedFarIncrement at h
  rw [show (1-e)/2=1-w by dsimp [e]; ring,show (1+e)/2=w by dsimp [e]; ring,
    show z-(1+e)*s=x by dsimp [e,z,s]; ring,show z+(1-e)*s=y by dsimp [e,z,s]; ring] at h
  have hv₀ : 0≤1-e^2 := by
    dsimp [e]
    nlinarith only [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  have hv := Real.rpow_le_rpow hv₀ (by linarith only [sq_nonneg e] : 1-e^2≤1)
    (show 0≤criticalQ/2 by linarith only [hq₀])
  rw [Real.one_rpow] at hv
  have hm := mul_le_mul hv (Real.rpow_le_rpow (abs_nonneg s) hs hq₀)
    (Real.rpow_nonneg (abs_nonneg s) _) (by norm_num : (0:ℝ)≤1)
  rw [one_mul,one64_pow_criticalQ] at hm
  exact h.trans hm

private theorem evenGap_chord_error {p a b w : ℝ} (hw : w∈Icc 0 1)
    (hab₀ : a≤b) (hab : b-a≤1/32) :
    (1-w)*balancedEvenGap criticalQ p a+w*balancedEvenGap criticalQ p b-
      balancedEvenGap criticalQ p ((1-w)*a+w*b) ≤ 1/729 := by
  have hAbs : |b-a|≤1/32 := by rwa [abs_of_nonneg (sub_nonneg.mpr hab₀)]
  have hPlus := weighted_power_error (x:=p+a) (y:=p+b) hw (by simpa only [add_sub_add_left_eq_sub] using hAbs)
  have hMinus := weighted_power_error (x:=p-a) (y:=p-b) hw (by
    rw [show p-b-(p-a)=-(b-a) by ring,abs_neg]; exact hAbs)
  rw [show (1-w)*(p+a)+w*(p+b)=p+((1-w)*a+w*b) by ring] at hPlus
  rw [show (1-w)*(p-a)+w*(p-b)=p-((1-w)*a+w*b) by ring] at hMinus
  unfold balancedEvenGap
  linarith only [hPlus,hMinus]

/-- An upper secant cost needs only endpoint tests, with a fixed chord error. -/
private theorem head_middle_interpolate {P H R T a b x L : ℝ} (hH : 0<H)
    (hR : 0≤R) (hT : 0≤T) (hax : a≤x) (hxb : x≤b) (hab : b-a≤1/32)
    (ha : R*max 0 ((balancedEvenGap criticalQ P ((1-H)*a+H)-balancedEvenGap criticalQ P a)/H)+T*a^2
      + R/(729*H) ≤ L)
    (hb : R*max 0 ((balancedEvenGap criticalQ P ((1-H)*b+H)-balancedEvenGap criticalQ P b)/H)+T*b^2
      + R/(729*H) ≤ L) :
    R*max 0 ((balancedEvenGap criticalQ P ((1-H)*x+H)-balancedEvenGap criticalQ P x)/H)+T*x^2 ≤ L := by
  let A := balancedEvenGap criticalQ P
  let Q := fun x : ℝ => (A ((1-H)*x+H)-A x)/H
  change R*max 0 (Q a)+T*a^2+R/(729*H)≤L at ha
  change R*max 0 (Q b)+T*b^2+R/(729*H)≤L at hb
  change R*max 0 (Q x)+T*x^2≤L
  obtain ⟨w,hw,hx⟩ := exists_interval_lerp hax hxb
  have hC := (evenGap_convex head_q_pos.le P).2 (mem_univ ((1-H)*a+H)) (mem_univ ((1-H)*b+H))
    (sub_nonneg.mpr hw.2) hw.1 (by ring : 1-w+w=1)
  simp only [smul_eq_mul,
    show (1-w)*((1-H)*a+H)+w*((1-H)*b+H)=(1-H)*((1-w)*a+w*b)+H by ring,←hx] at hC
  have hE := evenGap_chord_error (p:=P) hw (hax.trans hxb) hab
  rw [←hx] at hE
  have hApprox : Q x≤(1-w)*Q a+w*Q b+(1/729)/H := by
    dsimp [Q]
    have hh : (A ((1-H)*x+H)-A x)/H ≤
        ((1-w)*A ((1-H)*a+H)+w*A ((1-H)*b+H)
          -((1-w)*A a+w*A b)+(1/729))/H := by
      apply div_le_div_of_nonneg_right _ hH.le
      linarith only [hC,hE]
    exact hh.trans_eq (by ring)
  have hs : x^2≤(1-w)*a^2+w*b^2 := by
    rw [hx]
    nlinarith only [mul_nonneg (mul_nonneg hw.1 (sub_nonneg.mpr hw.2)) (sq_nonneg (a-b))]
  have hQ : max 0 (Q x) ≤ (1-w)*max 0 (Q a)+w*max 0 (Q b)+(1/729)/H := by
    apply max_le
    · exact add_nonneg (add_nonneg (mul_nonneg (sub_nonneg.mpr hw.2) (le_max_left _ _))
          (mul_nonneg hw.1 (le_max_left _ _))) (by positivity)
    · exact hApprox.trans (add_le_add_left
        (add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) (sub_nonneg.mpr hw.2))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hw.1)) _)
  have h1 := mul_le_mul_of_nonneg_left hQ hR
  have h2 := mul_le_mul_of_nonneg_left hs hT
  have h3 := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hw.2)
  have h4 := mul_le_mul_of_nonneg_left hb hw.1
  refine (add_le_add h1 h2).trans ?_
  have hsum := add_le_add h3 h4
  convert hsum using 1 <;> ring

end HlawkaSchatten.BelowExponent
