/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3SData
public import HlawkaSchatten.BelowExponent.G3SWide
public import HlawkaSchatten.BelowExponent.G3PCover

/-! Lift the transverse G3 integer witnesses to the actual real row inequality. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3S

noncomputable section

private theorem scale_bounds {x lo hi m : ℝ} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    min (lo * m) (hi * m) ≤ x * m ∧ x * m ≤ max (lo * m) (hi * m) := by
  rcases le_total 0 m with h | h
  · exact ⟨min_le_of_left_le (mul_le_mul_of_nonneg_right hlo h),
      le_max_of_le_right (mul_le_mul_of_nonneg_right hhi h)⟩
  · exact ⟨min_le_of_right_le (mul_le_mul_of_nonpos_right hhi h),
      le_max_of_le_left (mul_le_mul_of_nonpos_right hlo h)⟩

private theorem product_bounds {x y : ℝ} {a₀ a₁ b₀ b₁ : ℚ}
    (ha₀ : (a₀ : ℝ) ≤ x) (ha₁ : x ≤ (a₁ : ℝ))
    (hb₀ : (b₀ : ℝ) ≤ y) (hb₁ : y ≤ (b₁ : ℝ)) :
    (mulLo a₀ a₁ b₀ b₁ : ℝ) ≤ x * y ∧ x * y ≤ (mulHi a₀ a₁ b₀ b₁ : ℝ) := by
  have h₀ := scale_bounds (m := (a₀ : ℝ)) hb₀ hb₁
  have h₁ := scale_bounds (m := (a₁ : ℝ)) hb₀ hb₁
  simp only [mul_comm _ (a₀ : ℝ), mul_comm _ (a₁ : ℝ)] at h₀ h₁
  have h := scale_bounds (m := y) ha₀ ha₁
  simp only [mulLo, mulHi, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  exact ⟨(min_le_min h₀.1 h₁.1).trans h.1, h.2.trans (max_le_max h₀.2 h₁.2)⟩

theorem ratio_mono {x y : ℝ} (h : x ≤ y) (hy : y ≤ 1 / 5) :
    x / (2 - x) ≤ y / (2 - y) := by
  apply (div_le_div_iff₀ (by linarith : 0 < 2 - x) (by linarith : 0 < 2 - y)).2
  nlinarith only [h]

private theorem units_nonneg (n : Nat) : 0 ≤ units n := by unfold units; positivity

private theorem abs_power_mono {x y : ℝ} (h : |x| ≤ |y|) : power x ≤ power y :=
  Real.rpow_le_rpow (abs_nonneg x) h
    ((by norm_num : (0 : ℝ) ≤ 1054 / 665).trans criticalQ_bracket.1.le)

private theorem pow_nonneg_mono {x y : ℝ} (hx : 0 ≤ x) (h : x ≤ y) : power x ≤ power y := by
  apply abs_power_mono
  rwa [abs_of_nonneg hx, abs_of_nonneg (hx.trans h)]

theorem weight_bounds {B : Box} {slo shi : ℚ} {h σ : ℝ}
    (hh₀ : (B.lo 0 : ℝ) ≤ h) (hh₁ : h ≤ (B.hi 0 : ℝ))
    (hσ₀ : (B.lo 1 : ℝ) ≤ σ) (hσ₁ : σ ≤ (B.hi 1 : ℝ))
    (hlo : 0 ≤ B.lo 0) (hs : 0 ≤ B.lo 1)
    (hpowlo : 0 ≤ slo) (hpowhi : 0 ≤ shi)
    (wlo : G3Power.crossLE slo (B.lo 1) 25 12 = true)
    (whi : G3Power.crossLE (B.hi 1) shi 12 25 = true) :
    (weightLower B slo : ℝ) ≤ g3Weight h σ ∧ g3Weight h σ ≤ (weightUpper B shi : ℝ) := by
  have lowh : (0 : ℝ) ≤ (B.lo 0 : ℝ) := by exact_mod_cast hlo
  have lows : (0 : ℝ) ≤ (B.lo 1 : ℝ) := by exact_mod_cast hs
  have wlo₀ : (0 : ℝ) ≤ (slo : ℝ) := by exact_mod_cast hpowlo
  have whi₀ : (0 : ℝ) ≤ (shi : ℝ) := by exact_mod_cast hpowhi
  have hl := G3Power.crossLE_lower (by decide) wlo
  have hu := G3Power.crossLE_upper (by decide) whi
  rw [abs_of_nonneg lows, abs_of_nonneg wlo₀] at hl
  rw [abs_of_nonneg (lows.trans (hσ₀.trans hσ₁)), abs_of_nonneg whi₀] at hu
  norm_num at hl hu
  have hlo' := hl.trans (Real.rpow_le_rpow lows hσ₀ (by norm_num : (0 : ℝ) ≤ 12/25))
  have hhi' := (Real.rpow_le_rpow (lows.trans hσ₀) hσ₁ (by norm_num : (0 : ℝ) ≤ 12/25)).trans hu
  let bandσ : ℝ := if σ < 3 / 20 then 1 else 49 / 50
  let band₀ : ℝ := if B.hi 1 < 3 / 20 then 1 else 49 / 50
  let band₁ : ℝ := if B.lo 1 < 3 / 20 then 1 else 49 / 50
  have hband₀ : band₀ ≤ bandσ := by
    dsimp [band₀, bandσ]
    split <;> split <;> norm_num
    rename_i hs₁ hσ'
    have hs₁' : (B.hi 1 : ℝ) < 3 / 20 := by
      simpa using (Rat.cast_lt (K := ℝ)).2 hs₁
    exact (hσ' (hσ₁.trans_lt hs₁')).elim
  have hband₁ : bandσ ≤ band₁ := by
    dsimp [bandσ, band₁]
    split <;> split <;> norm_num
    rename_i hσ' hs₀
    have hs₀' := hσ₀.trans_lt hσ'
    exact (hs₀ <| (Rat.cast_lt (K := ℝ)).1 (by simpa using hs₀')).elim
  have hband₀' : 0 ≤ band₀ := by dsimp [band₀]; split <;> norm_num
  have hbandσ' : 0 ≤ bandσ := by dsimp [bandσ]; split <;> norm_num
  have hmul {a b u v x y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
      (hu : 0 ≤ u) (huv : u ≤ v) (hx : 0 ≤ x) (hxy : x ≤ y) :
      a * ((3 / 5) * (1 + u / 16)) * x ≤ b * ((3 / 5) * (1 + v / 16)) * y := by
    apply mul_le_mul _ hxy hx
      (mul_nonneg (ha.trans hab) (by linarith only [hu, huv]))
    exact mul_le_mul hab (by linarith only [huv]) (by linarith only [hu]) (ha.trans hab)
  have weight₀ : (weightLower B slo : ℝ) =
      band₀ * (3/5 * (1 + (B.lo 0 : ℝ) / 16)) * slo := by
    unfold weightLower coefficient
    dsimp [band₀]
    split <;> push_cast <;> rfl
  have weight₁ : (weightUpper B shi : ℝ) =
      band₁ * (3/5 * (1 + (B.hi 0 : ℝ) / 16)) * shi := by
    unfold weightUpper coefficient
    dsimp [band₁]
    split <;> push_cast <;> rfl
  rw [weight₀, weight₁]
  have w_eq : g3Weight h σ = bandσ * ((3 / 5) * (1 + h / 16)) * σ ^ (12 / 25 : ℝ) := by
    change bandσ * (3 / 5) * (1 + h / 16) * σ ^ (12 / 25 : ℝ) = _
    rw [mul_assoc bandσ (3 / 5)]
  rw [w_eq]
  exact ⟨hmul hband₀' hband₀ lowh hh₀ wlo₀ hlo',
    hmul hbandσ' hband₁ (lowh.trans hh₀) hh₁ (Real.rpow_nonneg (lows.trans hσ₀) _) hhi'⟩

private theorem affine_nonneg {L R N C μ : ℝ}
    (hL : L ≤ μ) (hR : μ ≤ R)
    (hl : 0 ≤ (1 - L) * N + L * C) (hr : 0 ≤ (1 - R) * N + R * C) :
    0 ≤ (1 - μ) * N + μ * C := by
  rcases le_total N C with h | h
  · have hm := mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr h)
    nlinarith only [hm, hl]
  · have hm := mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr h)
    nlinarith only [hm, hr]

theorem witness_sound {B : Box} {w : Witness} (hw : witnessOK B w = true)
    {h σ p z : ℝ} (hx : B.Mem ![h, σ, p, z])
    (hheight : h ≤ 1) (hσpos : 0 < σ) (hp : |p| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ p 1 z := by
  simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hw
  rcases hw with ⟨hB, wL, wR, wLT, wRT, wFT, wF0, wOT, wO0, wZ, wσ₀, wσ₁, wm₀, wm₁⟩
  obtain ⟨h00, h10, h11, h20, h21, hT⟩ := hB
  have hh := hx 0
  have hσ := hx 1
  have hpp := hx 2
  have hzz := hx 3
  change (B.lo 0 : ℝ) ≤ h ∧ h ≤ (B.hi 0 : ℝ) at hh
  change (B.lo 1 : ℝ) ≤ σ ∧ σ ≤ (B.hi 1 : ℝ) at hσ
  change (B.lo 2 : ℝ) ≤ p ∧ p ≤ (B.hi 2 : ℝ) at hpp
  change (B.lo 3 : ℝ) ≤ z ∧ z ≤ (B.hi 3 : ℝ) at hzz
  have hh0r : (0 : ℝ) ≤ (B.lo 0 : ℝ) := by exact_mod_cast h00
  have hh₀ : 0 ≤ h := hh0r.trans hh.1
  have hσ₁r : (B.hi 1 : ℝ) ≤ 1 / 5 := by
    simpa using (Rat.cast_le (K := ℝ)).2 h11
  have hσ₁ := hσ.2.trans hσ₁r
  let k := σ / (2 - σ)
  let μ := g3Weight h σ
  let a := 1 + k * (p - z)
  let T := (pathMax B : ℝ)
  have hk : 0 ≤ k := div_nonneg hσpos.le (by linarith only [hσ₁])
  have hk9 : k ≤ 1 / 9 := (div_le_iff₀ (by linarith only [hσ₁] : 0 < 2 - σ)).2
    (by linarith only [hσ₁])
  have ha : 0 ≤ a := by
    have hd : (-9 : ℝ) ≤ p - z := by linarith only [(abs_le.mp hp).1, (abs_le.mp hz).2]
    dsimp [a]
    linarith only [mul_le_mul_of_nonneg_left hd hk, hk9]
  have hμ := g3_weight_pos_lt_third hh₀ hheight hσpos hσ₁
  have hk₀ : (kMin B : ℝ) ≤ k := by
    unfold kMin ratio
    push_cast
    exact ratio_mono hσ.1 hσ₁
  have hk₁ : k ≤ (kMax B : ℝ) := by
    unfold kMax ratio
    push_cast
    exact ratio_mono hσ.2 hσ₁r
  have hpd₀ : ((B.lo 2 - B.hi 3 : ℚ) : ℝ) ≤ p - z := by
    push_cast
    exact sub_le_sub hpp.1 hzz.2
  have hpd₁ : p - z ≤ ((B.hi 2 - B.lo 3 : ℚ) : ℝ) := by
    push_cast
    exact sub_le_sub hpp.2 hzz.1
  have hprod := product_bounds hk₀ hk₁ hpd₀ hpd₁
  have ha₀ : (aMin B : ℝ) ≤ a := by
    simp only [aMin, Rat.cast_max, Rat.cast_zero, Rat.cast_add, Rat.cast_one, max_le_iff]
    exact ⟨ha, add_le_add_right hprod.1 1⟩
  have ha₁ : a ≤ (aMax B : ℝ) := by
    simp only [aMax, Rat.cast_add, Rat.cast_one]
    exact add_le_add_right hprod.2 1
  have ha₀r : (0 : ℝ) ≤ (aMin B : ℝ) := by simp [aMin, Rat.cast_max]
  have hT₀ : 0 < T := by dsimp [T]; exact_mod_cast hT
  have htT : h * a ≤ T := by
    dsimp [T, pathMax]
    push_cast
    exact mul_le_mul hh.2 ha₁ ha (hh₀.trans hh.2)
  have hU₀ : (farBase B : ℝ) ≤ z + h * a := by
    unfold farBase
    push_cast
    exact add_le_add hzz.1 (mul_le_mul hh.1 ha₀ ha₀r hh₀)
  have lowP (x y : ℚ) (hy : G3Power.lower x y = true) : (y : ℝ) ≤ power x :=
    G3Power.lower_sound hy
  have highP (x : ℚ) (y : Nat) (hy : G3Power.upper x (units y) = true) :
      power x ≤ (units y : ℝ) := G3Power.upper_sound (units_nonneg y) hy
  have eL := lowP _ _ wL
  have eR := lowP _ _ wR
  have eLT := highP _ _ wLT
  have eRT := highP _ _ wRT
  have eFT := highP _ _ wFT
  have eF0 := lowP _ _ wF0
  have eOT := highP _ _ wOT
  have eO0 := lowP _ _ wO0
  have eZ := highP _ _ wZ
  push_cast at eL eR eLT eRT eFT eOT
  change power (1 + (B.lo 2 : ℝ) - T) ≤ (units w.leftShift : ℝ) at eLT
  change power (1 - (B.hi 2 : ℝ) - T) ≤ (units w.rightShift : ℝ) at eRT
  change power ((B.hi 3 : ℝ) + T) ≤ (units w.farShift : ℝ) at eFT
  have powZ : power z ≤ (units w.zPower : ℝ) := by
    apply (abs_power_mono (y := (rowAbsMax B : ℝ)) _).trans eZ
    have hmax : (0 : ℝ) ≤ (rowAbsMax B : ℝ) := by
      simp only [rowAbsMax, Rat.cast_abs, Rat.cast_max]
      exact (abs_nonneg _).trans (le_max_left _ _)
    rw [abs_of_nonneg hmax]
    simp only [rowAbsMax, Rat.cast_max, Rat.cast_abs]
    rcases le_total 0 z with hz₀ | hz₀
    · exact (abs_of_nonneg hz₀ ▸ hzz.2).trans ((le_abs_self _).trans (le_max_right _ _))
    · rw [abs_of_nonpos hz₀]
      exact (neg_le_neg hzz.1).trans ((neg_le_abs _).trans (le_max_left _ _))
  have hp0r : (-1 : ℝ) ≤ (B.lo 2 : ℝ) := by exact_mod_cast h20
  have hp1r : (B.hi 2 : ℝ) ≤ 1 := by exact_mod_cast h21
  have hc : (core w : ℝ) ≤ pairMean p 1 - power z := by
    have hL := pow_nonneg_mono (x := 1 + (B.lo 2 : ℝ)) (y := 1 + p)
      (by linarith only [hp0r]) (by linarith only [hpp.1])
    have hR := pow_nonneg_mono (x := 1 - (B.hi 2 : ℝ)) (y := 1 - p)
      (by linarith only [hp1r]) (by linarith only [hpp.2])
    unfold core pairMean
    push_cast
    linarith only [eL, eR, hL, hR, powZ]
  have hN : (nearSlope B w : ℝ) ≤ nearSecant (B.lo 2) (B.hi 2) T := by
    unfold nearSlope nearSecant
    push_cast
    change _ / (2 * T) ≤ (_ / T + _ / T) / 2
    have div_eq (x y : ℝ) : (x / T + y / T) / 2 = (x + y) / (2 * T) := by
      field_simp [hT₀.ne']
    rw [div_eq]
    apply (div_le_div_iff_of_pos_right (show 0 < 2 * T by positivity)).2
    linarith only [eL, eR, eLT, eRT]
  have hF : farSecant (B.hi 3) T ≤ (farSlope B w : ℝ) := by
    unfold farSecant farSlope
    push_cast
    change _ / T ≤ _ / T
    exact (div_le_div_iff_of_pos_right hT₀).2 (by linarith only [eFT, eF0])
  have hn : (nearLow B w : ℝ) ≤ a * nearSecant (B.lo 2) (B.hi 2) T := by
    simp only [nearLow, Rat.cast_min, Rat.cast_mul]
    exact (scale_bounds (m := (nearSlope B w : ℝ)) ha₀ ha₁).1.trans
      (mul_le_mul_of_nonneg_left hN ha)
  have hG : (signedLow B w : ℝ) ≤ k * (core w : ℝ) - a * farSecant (B.hi 3) T -
      (power ((farBase B : ℝ) - 2) - power (farBase B : ℝ)) / 2 := by
    simp only [signedLow, Rat.cast_sub, Rat.cast_min, Rat.cast_max, Rat.cast_mul,
      Rat.cast_div, Rat.cast_ofNat]
    have hk' := (scale_bounds (m := (core w : ℝ)) hk₀ hk₁).1
    have hf' := (mul_le_mul_of_nonneg_left hF ha).trans
      (scale_bounds (m := (farSlope B w : ℝ)) ha₀ ha₁).2
    linarith only [hk', hf', eOT, eO0]
  have hw' := weight_bounds hh.1 hh.2 hσ.1 hσ.2 h00 h10
    (units_nonneg _) (units_nonneg _) wσ₀ wσ₁
  change (weightMin B w : ℝ) ≤ μ ∧ μ ≤ (weightMax B w : ℝ) at hw'
  have hm₀ : (0 : ℝ) ≤ (margin B w (weightMin B w) : ℝ) := by exact_mod_cast wm₀
  have hm₁ : (0 : ℝ) ≤ (margin B w (weightMax B w) : ℝ) := by exact_mod_cast wm₁
  simp only [margin, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_one] at hm₀ hm₁
  have hm := affine_nonneg hw'.1 hw'.2 hm₀ hm₁
  have hδ := lower_bound hh₀ hk ha hT₀ htT hpp.1 hpp.2 hzz.2 hU₀ hc
    hμ.1.le (hμ.2.le.trans (by norm_num))
  change h * ((1 - μ) * a * nearSecant (B.lo 2) (B.hi 2) T +
    μ * (k * (core w : ℝ) - a * farSecant (B.hi 3) T -
      (power ((farBase B : ℝ) - 2) - power (farBase B : ℝ)) / 2)) ≤ _ at hδ
  have hnonneg : 0 ≤ (1 - μ) * a * nearSecant (B.lo 2) (B.hi 2) T +
    μ * (k * (core w : ℝ) - a * farSecant (B.hi 3) T -
      (power ((farBase B : ℝ) - 2) - power (farBase B : ℝ)) / 2) := by
    have hnear := mul_le_mul_of_nonneg_left hn (show 0 ≤ 1 - μ by linarith only [hμ.2])
    have hfar := mul_le_mul_of_nonneg_left hG hμ.1.le
    nlinarith only [hm, hnear, hfar]
  exact (mul_nonneg hh₀ hnonneg).trans hδ

theorem tree_sound {B : Box} {t : Tree} (ht : t.ok B = true)
    {h σ p z : ℝ} (hx : B.Mem ![h, σ, p, z])
    (hheight : h ≤ 1) (hσpos : 0 < σ) (hp : |p| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ p 1 z := by
  induction t generalizing B with
  | cell witness => exact witness_sound ht hx hheight hσpos hp hz
  | cut axis lower upper ihLower ihUpper =>
    simp only [Tree.ok, Bool.and_eq_true] at ht
    rcases le_total (![h, σ, p, z] axis) (midpoint B axis : ℝ) with hl | hr
    · exact ihLower ht.1 (G3P.Box.mem_lower hx hl)
    · exact ihUpper ht.2 (G3P.Box.mem_upper hx hr)

end

end HlawkaSchatten.BelowExponent.G3S
