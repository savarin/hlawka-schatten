/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1Compact
public import HlawkaSchatten.BelowExponent.G1CompactData
import all HlawkaSchatten.BelowExponent.G1Compact
import all HlawkaSchatten.BelowExponent.G1CompactData
import all HlawkaSchatten.BelowExponent.G1Far

/-! The full G1 strip, with the written slab weights valid for every row. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set

open private g1Curvature compact_compensated_lower compact_gap_of_certificates from HlawkaSchatten.BelowExponent.G1Compact
open G1CompactData
open private qLo_le qHi_ge q_one compactBasicChecks compactParams_length_cast
  compactParams_radius_cast compact_inner_bound from HlawkaSchatten.BelowExponent.G1CompactData
open private slab_ranges from HlawkaSchatten.BelowExponent.G1Far

private theorem compactCurvature_bounds :
    (cLo : ℝ) ≤ g1Curvature ∧ g1Curvature ≤ (cHi : ℝ) := by
  unfold cLo cHi g1Curvature
  push_cast
  have hlo : 0 ≤ (qLo:ℝ)-1 := by norm_num [qLo]
  have hq : 0 ≤ criticalQ-1 := sub_nonneg.mpr q_one
  have hhi : 0 ≤ (qHi:ℝ) := by norm_num [qHi]
  have h := mul_le_mul qLo_le (sub_le_sub_right qLo_le 1) hlo (zero_le_one.trans q_one)
  have h' := mul_le_mul qHi_ge (sub_le_sub_right qHi_ge 1) hq hhi
  constructor <;> linarith only [h, h']

private theorem g1_compact_endpoint_bin (i : Fin 13) (right : Bool) (j : Fin 64) {e s z : ℝ}
    (he : e ∈ Icc 0 (1/2)) (heBin : e ∈ Icc (eNode j.castSucc : ℝ) (eNode j.succ : ℝ))
    (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    let P := compactParams i right j
    0 ≤ balancedFacetGap criticalQ (P.μ : ℝ) (P.l : ℝ) e 1 s z := by
  let P := compactParams i right j
  let l : ℝ := P.l
  let μ : ℝ := P.μ
  let E : ℝ := P.E
  let V : ℝ := P.V
  let T : ℝ := P.T
  let C : ℝ := P.C
  let k : ℝ := P.k
  let w : ℝ := P.w
  let α : ℝ := P.α
  let β : ℝ := P.β
  let Ppow : ℝ := P.powerUpper
  let a : ℝ := P.a
  let c := 1-μ*(1-l)
  let B := (1-μ)*T
  let R := E+9*l
  change 0 ≤ balancedFacetGap criticalQ μ l e 1 s z
  obtain ⟨hl, hl₁, hμ, hμ₁, hw, hw₁, hR, haC, _, hPow, hSupp, hFlank, _⟩ :=
    compactBasicChecks i right j
  have hlR : 0 ≤ l := by dsimp [l,P]; exact_mod_cast hl.le
  have hl₁R : l ≤ 1 := by dsimp [l,P]; exact_mod_cast hl₁.le
  have hμR : 0 < μ := by dsimp [μ,P]; exact_mod_cast hμ
  have hμ₁R : μ ≤ 1 := by dsimp [μ,P]; exact_mod_cast hμ₁.le
  have hwR : 0 < w := by dsimp [w,P]; exact_mod_cast hw
  have hw₁R : w ≤ 1 := by dsimp [w,P]; exact_mod_cast hw₁
  have heE : e ≤ E := heBin.2
  have hR₀ : 0 ≤ R := add_nonneg (he.1.trans heE) (by positivity)
  have hR₁ : R ≤ 1 := by
    dsimp [R, E, l, P]
    exact_mod_cast hR
  have hR₂ : 1-R^2 ≥ 0 := by
    have h : R^2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hR₀ hR₁ 2
    exact sub_nonneg.mpr h
  have hVeq : V = 1-(eNode j.castSucc : ℝ)^2 := by
    change ((1-(eNode j.castSucc)^2 : ℚ) : ℝ) = _
    push_cast
    rfl
  have heLo₀ : 0 ≤ (eNode j.castSucc : ℝ) := by
    unfold eNode
    push_cast
    positivity
  have heV : 1-e^2 ≤ V := by
    rw [hVeq]
    exact sub_le_sub_left (pow_le_pow_left₀ heLo₀ heBin.1 2) 1
  have hV₀ : 0 ≤ V := by
    have h : e^2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ he.1 (he.2.trans (by norm_num : (1/2:ℝ) ≤ 1)) 2
    exact (sub_nonneg.mpr h).trans heV
  have hT : g1Curvature+(1/2-g1Curvature)*R^2 ≤ T := by
    have hTeq : T = (cHi : ℝ)+(1/2-(cHi : ℝ))*R^2 := by
      change ((cHi+(1/2-cHi)*(P.E+9*P.l)^2 : ℚ) : ℝ) = _
      push_cast
      rfl
    rw [hTeq]
    nlinarith only [mul_nonneg (sub_nonneg.mpr compactCurvature_bounds.2) hR₂]
  have haeq : a = c*(cLo : ℝ)-B*E^2 := by
    change (((1-P.μ+P.μ*P.l)*cLo-(1-P.μ)*P.T*P.E^2 : ℚ) : ℝ) = _
    push_cast
    dsimp [c, μ, l, B, T, E]
    ring
  have hc : 0 ≤ c := by
    have h := mul_le_mul_of_nonneg_right hμ₁R (sub_nonneg.mpr hl₁R)
    dsimp [c]
    linarith only [h, hlR]
  have haCR : 0 < a-C := by dsimp [a,C,P]; exact_mod_cast haC
  have ha : a-C ≤ c*g1Curvature-B*E^2-C := by
    rw [haeq]
    linarith only [mul_le_mul_of_nonneg_left compactCurvature_bounds.1 hc]
  have hk : B+(B*E)^2/(c*g1Curvature-B*E^2-C) ≤ k := by
    have hkEq : k = B+(B*E)^2/(a-C) := by
      change (((1-P.μ)*P.T+((1-P.μ)*P.T*P.E)^2/(P.a-P.C) : ℚ) : ℝ) = _
      push_cast
      rfl
    rw [hkEq]
    exact add_le_add_right (div_le_div_of_nonneg_left (sq_nonneg _) haCR ha) _
  have hwPow : w^criticalQ ≤ Ppow := by
    have h := (natRat_rpow_le_iff (a := (compactWitness i right j).2.1) (m := 84) (n := 53)
      (by decide : 0 < wScale) (by decide : 0 < powerScale) (by decide)).mpr hPow
    have h' : w^(84/53:ℝ) ≤ Ppow := by
      simpa [w, Ppow, P, compactParams_radius_cast, wScale, compactParams] using h
    exact (Real.rpow_le_rpow_of_exponent_ge hwR hw₁R (by simpa [qLo] using qLo_le)).trans h'
  have hα : criticalQ/2*(w^criticalQ/w^2) ≤ α := by
    have heq : α = (qHi:ℝ)/2*(Ppow/w^2) := by
      change ((qHi/2*P.powerUpper/P.w^2 : ℚ) : ℝ) = _
      push_cast
      dsimp [Ppow,w]
      ring
    rw [heq]
    exact mul_le_mul (by linarith only [qHi_ge])
      (div_le_div_of_nonneg_right hwPow (sq_nonneg w))
      (div_nonneg (Real.rpow_nonneg hwR.le _) (sq_nonneg w)) (by norm_num [qHi])
  have hβ : (1-criticalQ/2)*w^criticalQ ≤ β := by
    have heq : β = (1-(qLo:ℝ)/2)*Ppow := by
      change (((1-qLo/2)*P.powerUpper : ℚ) : ℝ) = _
      push_cast
      rfl
    rw [heq]
    exact mul_le_mul (by linarith only [qLo_le]) hwPow (Real.rpow_nonneg hwR.le _)
      (by norm_num [qLo])
  have hS : μ*α*V ≤ C := by dsimp [μ,α,V,C,P]; exact_mod_cast hSupp
  have hF : k*l/μ ≤ g1Curvature*(1-l)*(27/64) := by
    have h : k*l/μ ≤ (cLo:ℝ)*(1-l)*(27/64) := by
      have hCast := (Rat.cast_le (K := ℝ)).mpr hFlank
      push_cast at hCast
      exact hCast
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right compactCurvature_bounds.1 (sub_nonneg.mpr hl₁R)) (by norm_num))
  have hClose : |balancedFarCenter l l 1 z| ≤ w →
      k*l^2/μ*(z-1)^2+β+α*(balancedFarCenter l l 1 z)^2 ≤ l+(1-l)*|z|^criticalQ := by
    simpa only [balancedFarCenter, mul_one] using compact_inner_bound i right j (z := z)
  exact compact_gap_of_certificates hμR hlR hl₁R hV₀ hwR hz hα hβ hS hF hClose
    (compact_compensated_lower hμR.le hμ₁R hlR hl₁R he.1 heE he.2 heV hR₁ hs hz
      hT (haCR.trans_le ha) hk)

private theorem g1_compact_endpoint_unit (i : Fin 13) (right : Bool) {e s z : ℝ}
    (he : e ∈ Icc 0 (1/2)) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ balancedFacetGap criticalQ (g1SlabWeight i)
      (if right then g1SlabRight i else g1SlabLeft i) e 1 s z := by
  have h₀ : (eNode 0 : ℝ) ≤ e := by
    simpa [eNode] using he.1
  have h₁ : e ≤ (eNode (Fin.last 64) : ℝ) := by
    have hEnd : (eNode (Fin.last 64) : ℝ) = 1/2 := by norm_num [eNode, Fin.last]
    rw [hEnd]
    exact he.2
  obtain ⟨j, hj₀, hj₁⟩ := exists_adjacent_knots 63 (f := fun k => (eNode k : ℝ)) h₀ h₁
  have h := g1_compact_endpoint_bin i right j he ⟨hj₀,hj₁⟩ hs hz
  change 0 ≤ balancedFacetGap criticalQ ((compactParams i right j).μ : ℝ)
    ((compactParams i right j).l : ℝ) e 1 s z at h
  rw [compactParams_length_cast] at h
  have hW : ((compactParams i right j).μ : ℝ) = g1SlabWeight i := by
    change (((g1WeightNumerator i : ℚ)/1000 : ℚ) : ℝ) = _
    push_cast
    rfl
  rw [hW] at h
  cases right <;> exact h

private theorem g1_compact_endpoint (i : Fin 13) (right : Bool) {e p s z : ℝ}
    (he : e ∈ Icc 0 (1/2)) (hs : |s| ≤ |p|) (hz : |z| ≤ 8*|p|) :
    0 ≤ balancedFacetGap criticalQ (g1SlabWeight i)
      (if right then g1SlabRight i else g1SlabLeft i) e p s z := by
  let l := if right then g1SlabRight i else g1SlabLeft i
  by_cases hp : p = 0
  · have hs₀ : s = 0 := by simpa [hp] using hs
    have hz₀ : z = 0 := by simpa [hp] using hz
    subst p
    subst s
    subst z
    have hq : criticalQ ≠ 0 := by linarith only [q_one]
    simp [balancedFacetGap, balancedJensenGap, balancedEvenGap, balancedFarIncrement,
      balancedFarCenter, balancedNearShift, Real.zero_rpow hq]
  have hp' := abs_pos.mpr hp
  have hs' : |s/p| ≤ 1 := by rw [abs_div]; exact (div_le_one₀ hp').mpr hs
  have hz' : |z/p| ≤ 8 := by rw [abs_div]; exact (div_le_iff₀ hp').mpr hz
  have h := (balancedFacetGap_nonneg_scale_iff hp criticalQ (g1SlabWeight i) l e 1 (s/p) (z/p)).mpr
    (g1_compact_endpoint_unit i right he hs' hz')
  simpa only [mul_one, mul_div_cancel₀ _ hp] using h

/-- The compact bounded-z chart, on every closed G1 slab with its original weight. -/
theorem g1_slab_compact_gap (i : Fin 13) {l e p s z : ℝ}
    (hl₀ : g1SlabLeft i ≤ l) (hl₁ : l ≤ g1SlabRight i)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2) (hz : |z| ≤ 8*|p|) (hs : |s| ≤ |p|) :
    0 ≤ balancedFacetGap criticalQ (g1SlabWeight i) l e p s z := by
  obtain ⟨a, ha, rfl⟩ := exists_interval_lerp hl₀ hl₁
  obtain ⟨_, _, _, hμ, hμ₁⟩ := slab_ranges i
  have he : |e| ≤ 1 := by rw [abs_of_nonneg he₀]; linarith
  exact balancedFacetGap_nonneg_lerp q_one ha.1 ha.2 hμ.le (hμ₁.trans (by norm_num)) he
    (g1_compact_endpoint i false ⟨he₀,he₁⟩ hs hz) (g1_compact_endpoint i true ⟨he₀,he₁⟩ hs hz)

/-- The written G1 slab weight controls every real row on the upper facet. -/
theorem g1_slab_gap (i : Fin 13) {l e p s z : ℝ}
    (hl₀ : g1SlabLeft i ≤ l) (hl₁ : l ≤ g1SlabRight i) (he₀ : 0 ≤ e) (he₁ : e ≤ 1/2) :
    0 ≤ balancedFacetGap criticalQ (g1SlabWeight i) l e p s z := by
  by_cases hfar : 8*|p| ≤ |z|
  · have h := g1_slab_far_gap i (s := s) hl₀ hl₁ he₀ he₁ hfar
    obtain ⟨hL, _, _, hμ, _⟩ := slab_ranges i
    exact (mul_nonneg (mul_nonneg (div_nonneg hμ.le (by norm_num)) (hL.le.trans hl₀))
      (Real.rpow_nonneg (abs_nonneg _) _)).trans h
  · have hz := (lt_of_not_ge hfar).le
    by_cases hs : |p| ≤ |s|
    · exact (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/512) (Real.rpow_nonneg (abs_nonneg _) _)).trans
        (g1_slab_bounded_z_large_s_gap i hl₀ hl₁ he₀ he₁ hz hs)
    · exact g1_slab_compact_gap i hl₀ hl₁ he₀ he₁ hz (lt_of_not_ge hs).le

/-- The full G1 row certificate on the written balanced edge strip. -/
theorem rowAt_g1 {t : Profile} (ht : IsSimplex t)
    (hl₀ : 1/4096 ≤ t 2 + t 3) (hl₁ : t 2 + t 3 ≤ 74/4096)
    (he₀ : 0 ≤ t 0 - t 1) (he₁ : t 0 - t 1 ≤ 1/2) : RowAt criticalQ t := by
  let f (i : Fin 14) : ℝ := (g1LengthNumerator i : ℝ)/4096
  have h₀ : f 0 ≤ t 2+t 3 := by simpa [f, g1LengthNumerator] using hl₀
  have h₁ : t 2+t 3 ≤ f (Fin.last 13) := by simpa [f, g1LengthNumerator, Fin.last] using hl₁
  obtain ⟨i, hL, hU⟩ := exists_adjacent_knots 12 h₀ h₁
  obtain ⟨_, _, _, hμ, hμ₁⟩ := slab_ranges i
  exact rowAt_of_balancedFacetGap q_one ht hμ.le (hμ₁.trans (by norm_num))
    fun _ _ _ => g1_slab_gap i hL hU he₀ he₁

end HlawkaSchatten.BelowExponent
