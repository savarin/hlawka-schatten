/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3
public import HlawkaSchatten.BelowExponent.G1Compact
import all HlawkaSchatten.BelowExponent.G3
import all HlawkaSchatten.BelowExponent.G1Compact
import all HlawkaSchatten.BelowExponent.G1Far
import all HlawkaSchatten.BelowExponent.G1

/-! The G3 equality cone in the normalized p=1 chart. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set

open private g3_k_max from HlawkaSchatten.BelowExponent.G3
open private g1Curvature g1Curvature_nonneg g1Curvature_le_half g1_evenGap_abs_bounds from HlawkaSchatten.BelowExponent.G1Compact
open private criticalQ_lo criticalQ_hi from HlawkaSchatten.BelowExponent.G1Far
open private evenGap_convex half_pow_q from HlawkaSchatten.BelowExponent.G1

private theorem adjustedPower_first_deriv (c : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y^criticalQ-c*y^2) (criticalQ*x^(criticalQ-1)-2*c*x) x := by
  have h := (Real.hasDerivAt_rpow_const (x := x) (p := criticalQ) (Or.inl hx.ne')).sub
    (((hasDerivAt_id x).pow 2).const_mul c)
  convert! h using 1
  simp
  ring

private theorem adjustedPower_second_deriv (c : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => criticalQ*y^(criticalQ-1)-2*c*y)
      (2*g1Curvature*x^(criticalQ-2)-2*c) x := by
  have h := ((Real.hasDerivAt_rpow_const (x := x) (p := criticalQ-1) (Or.inl hx.ne')).const_mul
    criticalQ).sub ((hasDerivAt_id x).const_mul (2*c))
  convert! h using 1
  simp [g1Curvature, show criticalQ-1-1=criticalQ-2 by ring]
  ring

private theorem adjustedPower_continuous (c : ℝ) :
    Continuous (fun y : ℝ => y^criticalQ-c*y^2) :=
  (Real.continuous_rpow_const (by linarith [criticalQ_lo])).sub (continuous_const.mul (continuous_id.pow 2))

private theorem g3_half_pow_pred : (1/2:ℝ)^(criticalQ-2) = 4/3 := by
  rw [Real.rpow_sub (by norm_num : 0 < (1/2:ℝ)), half_pow_q, Real.rpow_two]
  norm_num

private theorem g3_far_quadratic {h Z s : ℝ} (hh₀ : 0 ≤ h) (hh₁ : h ≤ 1)
    (hZ : 3/4 ≤ Z) (hs : |s| ≤ 1/8) :
    balancedFarIncrement criticalQ (1-h) Z s ≤ (4/3)*g1Curvature*h*(2-h)*s^2 := by
  let c := (4/3)*g1Curvature
  have hq₂ : criticalQ ≤ 2 := criticalQ_hi.trans (by norm_num)
  have hc : ConcaveOn ℝ (Ici (1/2 : ℝ)) (fun x => x^criticalQ-c*x^2) := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos
      (f' := fun x => criticalQ*x^(criticalQ-1)-2*c*x)
      (f'' := fun x => 2*g1Curvature*x^(criticalQ-2)-2*c)
      (convex_Ici _) (adjustedPower_continuous c).continuousOn ?_ ?_ ?_
    · intro x hx
      rw [interior_Ici] at hx
      exact (adjustedPower_first_deriv c ((by norm_num : (0:ℝ) < 1/2).trans hx)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (adjustedPower_second_deriv c ((by norm_num : (0:ℝ) < 1/2).trans hx)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hp := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1/2) hx.le (sub_nonpos.mpr hq₂)
      rw [g3_half_pow_pred] at hp
      have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) g1Curvature_nonneg)
      dsimp [c]
      linarith only [hm]
  let a := h/2
  let b := 1-h/2
  let X := Z-(2-h)*s
  let Y := Z+h*s
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hab : a+b=1 := by dsimp [a,b]; ring
  have hX : 1/2 ≤ X := by
    dsimp [X]
    have hu := mul_le_mul_of_nonneg_left (abs_le.mp hs).2 (by linarith : 0 ≤ 2-h)
    nlinarith only [hu, hh₀, hZ]
  have hY : 1/2 ≤ Y := by
    dsimp [Y]
    have hL := mul_le_mul_of_nonneg_left (abs_le.mp hs).1 hh₀
    nlinarith only [hL, hh₁, hZ]
  have hmean : a*X+b*Y=Z := by dsimp [a,b,X,Y]; ring
  have hvar : a*X^2+b*Y^2-Z^2=h*(2-h)*s^2 := by dsimp [a,b,X,Y]; ring
  have hj := hc.2 (mem_Ici.mpr hX) (mem_Ici.mpr hY) ha hb hab
  simp only [smul_eq_mul, hmean] at hj
  have hZ₀ : 0 ≤ Z := by linarith
  unfold balancedFarIncrement
  rw [show (1-(1-h))/2=a by dsimp [a]; ring,
    show (1+(1-h))/2=b by dsimp [b]; ring,
    show Z-(1+(1-h))*s=X by dsimp [X]; ring,
    show Z+(1-(1-h))*s=Y by dsimp [Y]; ring]
  rw [abs_of_nonneg (by linarith : 0 ≤ X), abs_of_nonneg (by linarith : 0 ≤ Y), abs_of_nonneg hZ₀]
  have hv := congrArg (c * ·) hvar
  change a*X^criticalQ+b*Y^criticalQ-Z^criticalQ ≤ c*h*(2-h)*s^2
  linarith only [hj,hv]

private theorem g3_jensen_quadratic {l z : ℝ} (hl₀ : 0 ≤ l) (hl₁ : l ≤ 1)
    (hz : |z-1| ≤ 1/4) :
    g1Curvature*(5/4:ℝ)^(criticalQ-2)*l*(1-l)*(z-1)^2 ≤
      balancedJensenGap criticalQ l 1 z := by
  let c := g1Curvature*(5/4:ℝ)^(criticalQ-2)
  have hq₂ : criticalQ ≤ 2 := criticalQ_hi.trans (by norm_num)
  have hc : ConvexOn ℝ (Icc (3/4:ℝ) (5/4)) (fun x => x^criticalQ-c*x^2) := by
    refine convexOn_of_hasDerivWithinAt2_nonneg
      (f' := fun x => criticalQ*x^(criticalQ-1)-2*c*x)
      (f'' := fun x => 2*g1Curvature*x^(criticalQ-2)-2*c)
      (convex_Icc _ _) (adjustedPower_continuous c).continuousOn ?_ ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (adjustedPower_first_deriv c ((by norm_num : (0:ℝ) < 3/4).trans hx.1)).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (adjustedPower_second_deriv c ((by norm_num : (0:ℝ) < 3/4).trans hx.1)).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hp := Real.rpow_le_rpow_of_nonpos ((by norm_num : (0:ℝ) < 3/4).trans hx.1)
        hx.2.le (sub_nonpos.mpr hq₂)
      have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) g1Curvature_nonneg)
      dsimp [c]
      linarith only [hm]
  have hzz : z ∈ Icc (3/4:ℝ) (5/4) :=
    ⟨by linarith only [(abs_le.mp hz).1], by linarith only [(abs_le.mp hz).2]⟩
  have hx : 0 ≤ (1-l)*z+l := add_nonneg
    (mul_nonneg (sub_nonneg.mpr hl₁) (by linarith [hzz.1])) hl₀
  have hj := hc.2 hzz (show (1:ℝ) ∈ Icc (3/4:ℝ) (5/4) by norm_num)
    (sub_nonneg.mpr hl₁) hl₀ (by ring : 1-l+l=1)
  simp only [smul_eq_mul, mul_one, one_pow, Real.one_rpow] at hj
  unfold balancedJensenGap balancedFarCenter
  rw [abs_one, Real.one_rpow, mul_one, abs_of_nonneg (by linarith [hzz.1]), abs_of_nonneg hx]
  change c*l*(1-l)*(z-1)^2 ≤ (1-l)*z^criticalQ+l-((1-l)*z+l)^criticalQ
  linarith only [hj, show (1-l)*(c*z^2)+l*c-c*((1-l)*z+l)^2 = c*l*(1-l)*(z-1)^2 by ring]

private theorem g3_cone_curvature {l : ℝ} (hl : l ≤ 1/16) :
    1/4 ≤ g1Curvature*(5/4:ℝ)^(criticalQ-2)*(1-l) := by
  have hq : 3/2 ≤ criticalQ := by linarith [criticalQ_lo]
  have hc : 3/8 ≤ g1Curvature := by
    have h := mul_le_mul hq (show (1/2:ℝ) ≤ criticalQ-1 by linarith)
      (by norm_num) (by linarith)
    unfold g1Curvature
    linarith only [h]
  have hpow : (8/9:ℝ) ≤ (5/4:ℝ)^(criticalQ-2) := by
    have h := (le_natRat_rpow_iff (a := 4) (c := 8) (m := 1) (n := 2)
      (by decide : 0 < (5:ℕ)) (by decide : 0 < (9:ℕ)) (by decide)).mpr (by decide)
    have h' : (8/9:ℝ) ≤ (4/5:ℝ)^(1/2:ℝ) := by simpa only [Nat.cast_one, Nat.cast_ofNat] using h
    have heq : (4/5:ℝ)^(1/2:ℝ)=(5/4:ℝ)^(-(1/2):ℝ) := by
      rw [Real.rpow_neg (by norm_num)]
      rw [← Real.inv_rpow (by norm_num : (0:ℝ) ≤ 5/4)]
      norm_num
    rw [heq] at h'
    exact h'.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  have h₁ : (15/16:ℝ) ≤ 1-l := by linarith
  have hm : (3/8)*(8/9)*(15/16:ℝ) ≤ g1Curvature*(5/4:ℝ)^(criticalQ-2)*(1-l) :=
    mul_le_mul (mul_le_mul hc hpow (by norm_num) g1Curvature_nonneg) h₁
      (by norm_num) (by positivity)
  exact (by norm_num : (1/4:ℝ) ≤ (3/8)*(8/9)*(15/16)).trans hm

/-- The written equality cone in the p=1 G3 chart, with the common weight
used in the head and transverse charts. -/
theorem g3_equality_cone_gap {h σ s z : ℝ}
    (hh : 0 < h) (hσ : 0 < σ) (hσ₁ : σ ≤ 1/5) (hh₁ : h ≤ 1/(2-σ/(2-σ)))
    (hs : |s| ≤ 1/8) (hz : |z-1| ≤ 1/4) :
    0 ≤ g3FacetGap h σ 1 s z := by
  let k := σ/(2-σ)
  let l := h*k
  let μ := g3Weight h σ
  let b := 1-μ
  let w := k*(z-1)
  let v := (1-h)*s+h*w
  let Z := balancedFarCenter l l 1 z
  let J := balancedJensenGap criticalQ l 1 z
  let H := balancedFarIncrement criticalQ (1-h) Z s
  let A := balancedEvenGap criticalQ 1
  let C := g1Curvature
  have hq : 1 ≤ criticalQ := by linarith [criticalQ_lo]
  have hk : 0 < k := div_pos hσ (by linarith)
  have hk₁ : k ≤ 1/9 := g3_k_max hσ₁
  have hh' : h ≤ 1 := (g3_h_max hσ₁ hh₁).trans (by norm_num)
  have hl : 0 < l := mul_pos hh hk
  have hl₁ : l ≤ 1/16 := by
    have hm := mul_le_mul (g3_h_max hσ₁ hh₁) hk₁ hk.le (by norm_num : (0:ℝ) ≤ 9/17)
    dsimp [l]
    linarith only [hm]
  have hl' : l ≤ 1 := hl₁.trans (by norm_num)
  have hμ := g3_weight_pos_lt_third hh.le hh' hσ hσ₁
  have hb : 0 ≤ b := by dsimp [b, μ]; linarith only [hμ.2]
  have hZ : 3/4 ≤ Z := by
    have hz' : (3/4:ℝ) ≤ z := by linarith only [(abs_le.mp hz).1]
    have hM := mul_le_mul_of_nonneg_left hz' (sub_nonneg.mpr hl')
    unfold Z balancedFarCenter
    linarith only [hM, hl.le]
  have hFar : H/h ≤ (4/3)*C*(2-h)*s^2 := by
    apply (div_le_iff₀ hh).2
    linarith only [g3_far_quadratic hh.le hh' hZ hs]
  have hJ : C*(5/4:ℝ)^(criticalQ-2)*(1-l)*(z-1)^2 ≤ J/l := by
    apply (le_div_iff₀ hl).2
    linarith only [g3_jensen_quadratic hl.le hl' hz]
  have hNear : A s-A w ≤ (A s-A v)/h := by
    have hc := (evenGap_convex hq 1).2 (mem_univ s) (mem_univ w)
      (sub_nonneg.mpr hh') hh.le (by ring : 1-h+h=1)
    simp only [smul_eq_mul] at hc
    apply (le_div_iff₀ hh).2
    linarith only [hc]
  have hA : C*s^2 ≤ A s := (g1_evenGap_abs_bounds (hs.trans (by norm_num))).1
  have hw : |w| ≤ 1 := by
    dsimp [w]
    rw [abs_mul, abs_of_pos hk]
    exact (mul_le_mul hk₁ hz (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hW : A w ≤ (1/2)*w^2 := by
    have hw₂ : w^2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg w) hw 2
    have hU := (g1_evenGap_abs_bounds hw).2
    have h₄ : w^4 ≤ w^2 := by
      have hm := mul_le_mul_of_nonneg_right hw₂ (sq_nonneg w)
      linarith only [hm, show w^4=w^2*w^2 by ring]
    have hprod := mul_le_mul_of_nonneg_left h₄ (sub_nonneg.mpr g1Curvature_le_half)
    linarith only [hU,hprod]
  have hC := g3_cone_curvature hl₁
  have hS := g3_weight_cone_transverse hh.le hσ hσ₁
  have hRatio := (div_lt_iff₀ hμ.1).mp (g3_cornerK_div_weight hh.le hh' hσ hσ₁)
  have hCost : b*k ≤ (1/2)*μ := by
    have hn := mul_le_mul_of_nonneg_right (show b ≤ 1 by dsimp [b,μ]; linarith only [hμ.1]) hk.le
    linarith only [hn,hRatio]
  have hS₀ : 0 ≤ C*(1-μ*(1-k+(4/3)*(2-h)))*s^2 :=
    mul_nonneg (mul_nonneg g1Curvature_nonneg (sub_nonneg.mpr hS.le)) (sq_nonneg _)
  have hZ₀ : b*w^2/2 ≤ μ*k*(J/l) := by
    have hc := mul_le_mul_of_nonneg_right hC (sq_nonneg (z-1))
    have hmid : (1/4)*(z-1)^2 ≤ J/l := by linarith only [hc,hJ]
    have hu := mul_le_mul_of_nonneg_left hmid (mul_nonneg hμ.1.le hk.le)
    have hw' := mul_le_mul_of_nonneg_right hCost (mul_nonneg hk.le (sq_nonneg (z-1)))
    dsimp [w]
    linarith only [hu,hw']
  have hA' := mul_le_mul_of_nonneg_left hA (mul_nonneg hμ.1.le hk.le)
  change μ*k*(C*s^2) ≤ μ*k*A s at hA'
  have hF' := mul_le_mul_of_nonneg_left hFar hμ.1.le
  change μ*(H/h) ≤ μ*((4/3)*C*(2-h)*s^2) at hF'
  have hN' := mul_le_mul_of_nonneg_left hNear hb
  have hN'' := mul_le_mul_of_nonneg_left (sub_le_sub hA hW) hb
  have hEq : balancedNearShift l (1-h) l 1 s z = v := by
    rw [balancedNearShift_facet]
    dsimp [l,v,w]
    ring
  have hIdent := balancedFacetGap_div_h criticalQ μ h k 1 s z hh.ne' hk.ne'
  change balancedFacetGap criticalQ μ l (1-h) 1 s z / h =
    μ*k*(J/l+A s) + b*(A s-A (balancedNearShift l (1-h) l 1 s z))/h - μ*H/h at hIdent
  rw [hEq] at hIdent
  have hOut : 0 ≤ balancedFacetGap criticalQ μ l (1-h) 1 s z / h := by
    rw [hIdent]
    have hRewrite : C*(1-μ*(1-k+(4/3)*(2-h)))*s^2 =
        μ*k*(C*s^2)+b*(C*s^2)-μ*((4/3)*C*(2-h)*s^2) := by dsimp [b]; ring
    rw [hRewrite] at hS₀
    refine hS₀.trans ?_
    have hN := hN''.trans hN'
    have hSum := sub_le_sub (add_le_add (add_le_add hZ₀ hA') hN) hF'
    convert hSum using 1 <;> ring
  exact (by simpa only [zero_mul] using (le_div_iff₀ hh).mp hOut :
    0 ≤ balancedFacetGap criticalQ μ l (1-h) 1 s z)

end HlawkaSchatten.BelowExponent
