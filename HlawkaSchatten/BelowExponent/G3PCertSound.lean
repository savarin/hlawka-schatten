/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCertNear

/-! End-to-end reflection for adaptive central-chart rows of G3. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

open Vertex (RatBounds)

noncomputable section

private theorem clearDen_eval (a b c : ℚ) (θ : ℝ) :
    (clearDen a b c).eval θ = (a : ℝ) * θ ^ 2 + (b : ℝ) * θ + (c : ℝ) := by
  have ha : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
  have hb : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.den_pos.ne'
  have hc : (c.den : ℝ) ≠ 0 := by exact_mod_cast c.den_pos.ne'
  simp only [clearDen, Quad.eval, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, Rat.cast_def]
  field_simp [ha, hb, hc]

private theorem rowQuad_eval (B : Box) (positive : Bool) (w : RowWitness) {θ u : ℝ}
    (hu : u = (B.lo 2 : ℝ) + θ * ((B.hi 2 : ℝ) - (B.lo 2 : ℝ))) :
    (rowQuad B positive w).eval θ =
      (adjustedLeading B positive w : ℝ) * u ^ 2 -
        ((nearTerms B positive w).linearCost : ℝ) * u +
        ((nearTerms B positive w).constant : ℝ) -
        ((1 - θ) * (((chordCosts B positive w).1 : ℚ) : ℝ) + θ * (((chordCosts B positive w).2 : ℚ) : ℝ)) := by
  unfold rowQuad
  change (clearDen _ _ _).eval θ = _
  rw [clearDen_eval, hu]
  push_cast
  ring

private theorem winner_le_gap {B : Box} {w : RowWitness} (positive : Bool)
    {h σ u z θ : ℝ}
    (hh : 0 < h) (hh₁ : h ≤ 1) (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5)
    (hu : 0 ≤ u) (hu₁ : u ≤ 1) (hz : |z| ≤ 8)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hθ : u = B.lo 2 + θ * (B.hi 2 - (B.lo 2 : ℝ)))
    (hH : (bounds B 0).Contains h) (hU : (bounds B 2).Contains u)
    (hZ : (bounds B 3).Contains z)
    (hK : (kBounds B).Contains (σ / (2 - σ)))
    (hM : (muBounds B w).Contains (g3Weight h σ))
    (hJ : (w.jensen.value B : ℝ) ≤ g3DividedJensen (h * (σ / (2 - σ))) z)
    (hC : (center B).Contains (balancedFarCenter (h * (σ / (2 - σ))) (h * (σ / (2 - σ))) 1 z))
    (hfar : w.far.ok B positive = true)
    (hlou : 0 ≤ B.lo 2) (hhiu : 0 ≤ B.hi 2) :
    (rowQuad B positive w).eval θ ≤ g3FacetGap h σ 1 (signed positive u) z / h := by
  let μ := g3Weight h σ
  let s := signed positive u
  let k := σ / (2 - σ)
  let C := balancedFarCenter (h * k) (h * k) 1 z
  have hμ := (g3_weight_pos_lt_third hh.le hh₁ hσ hσ₁).1.le
  rw [rowQuad_eval B positive w hθ]
  cases hW : w.far with
  | chord ff a b =>
    rw [hW] at hfar
    simp only [FarWitness.ok, Bool.and_eq_true, and_assoc] at hfar
    obtain ⟨hf, ha, hb⟩ := hfar
    have h₁ := G3Power.tightUpper_sound (units_nonneg a) ha
    have h₂ := G3Power.tightUpper_sound (units_nonneg b) hb
    have hlu : (0 : ℝ) ≤ B.lo 2 := by exact_mod_cast hlou
    have hhu : (0 : ℝ) ≤ B.hi 2 := by exact_mod_cast hhiu
    rw [abs_of_nonneg hlu] at h₁
    rw [abs_of_nonneg hhu] at h₂
    have hchord : u ^ criticalQ ≤ (1 - θ) * (units a : ℝ) + θ * (units b : ℝ) := by
      apply rpow_le_upperChord
        ((by norm_num : (1 : ℝ) ≤ 1054 / 665).trans criticalQ_bracket.1.le)
        hlu hhu hu hθ₀ hθ₁ _ h₁ h₂
      rw [hθ]
      ring_nf
      rfl
    have hF := far_factor_sound hf hh hH hC hU hu
    have hf₀ : (0 : ℝ) ≤ (ff.value B positive : ℝ) := by exact_mod_cast factor_nonneg B positive ff
    have ht := near_sound positive hh hh₁ hσ hσ₁ hu hu₁ hz hH hU hZ hK hM hJ hF
    have hcost : μ * ((ff.value B positive : ℝ) * u ^ criticalQ) ≤
        (1 - θ) * (((chordCosts B positive w).1 : ℚ) : ℝ) + θ * (((chordCosts B positive w).2 : ℚ) : ℝ) := by
      simp only [chordCosts, hW, Rat.cast_mul]
      have hcoef := mul_le_mul_of_nonneg_right hM.2 hf₀
      have hpow := (mul_le_mul_of_nonneg_left hchord (le_trans
        (mul_nonneg hμ hf₀) hcoef))
      have hcost' := (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hu _)).trans hpow
      change μ * (ff.value B positive : ℝ) * u ^ criticalQ ≤ _ at hcost'
      convert hcost' using 1 <;> ring
    simp only [adjustedLeading, hW]
    exact (sub_le_sub_left hcost _).trans ht
  | variance n =>
    rw [hW] at hfar
    simp only [FarWitness.ok, Bool.and_eq_true, decide_eq_true_eq] at hfar
    have hcurve := curve_sound hfar.1 hfar.2 hC
    have hh' : 0 ≤ 2 - h := by linarith
    have hcoef : 0 ≤ criticalQ / 2 * (2 - h) := mul_nonneg
      (by linarith only [criticalQ_bracket.1]) hh'
    have hs₂ : s ^ 2 = u ^ 2 := by rw [← sq_abs s, signed_abs positive hu]
    have hF := g3FarIncrement_div_le_quadratic (s := s) hh hh₁ hcurve.1
    rw [hs₂] at hF
    have hFF := hF.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcurve.2 hcoef)
      (sq_nonneg u))
    have ht := near_sound positive hh hh₁ hσ hσ₁ hu hu₁ hz hH hU hZ hK hM hJ hFF
    have htwo : (point 2).Contains (2 : ℝ) := by simpa using point_has 2
    have hm := RatBounds.mul_mem (RatBounds.mul_mem (RatBounds.mul_mem hM q_mem)
      (point_has (1/2))) (RatBounds.mul_mem (RatBounds.sub_mem htwo hH) (point_has (units n)))
    have hmb : μ * (criticalQ / 2 * (2 - h) * (units n : ℝ)) ≤ (varianceCost B w n).hi := by
      have hc := hm.2
      change μ * criticalQ * (((1/2 : ℚ) : ℝ)) * ((2-h) * (units n : ℝ)) ≤
        (varianceCost B w n).hi at hc
      push_cast at hc
      convert hc using 1
      ring
    have hn := mul_le_mul_of_nonneg_right hmb (sq_nonneg u)
    let A := nearTerms B positive w
    let P := (A.squared : ℝ) * u ^ 2 - (A.linearCost : ℝ) * u + (A.constant : ℝ)
    have ht' : P - (μ * (criticalQ / 2 * (2 - h) * (units n : ℝ))) * u ^ 2 ≤
        g3FacetGap h σ 1 (signed positive u) z / h := by
      convert ht using 1
      dsimp only [P, μ]
      ring
    simp only [adjustedLeading, chordCosts, hW, Rat.cast_sub, Rat.cast_zero, mul_zero, add_zero,
      sub_zero]
    convert (sub_le_sub_left hn P).trans ht' using 1
    dsimp only [P, A]
    ring

theorem row_sound {B : Box} {w : RowWitness} (positive : Bool)
    {h σ u z : ℝ} (hw : rowOK B positive w = true)
    (hx : B.Mem ![h, σ, u, z]) (hh : 0 < h) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 (signed positive u) z := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hw
  obtain ⟨domain, wlo, whi, jw, fw, qw⟩ := hw
  obtain ⟨h0, h1, h2, s0, s1, l0, l1, u0, uw, u1⟩ := domain
  have hhB : (bounds B 0).Contains h := hx 0
  have hσB : (bounds B 1).Contains σ := hx 1
  have huB : (bounds B 2).Contains u := hx 2
  have hzB : (bounds B 3).Contains z := hx 3
  have hh₁ : h ≤ 1 := hhB.2.trans (by
    change (B.hi 0 : ℝ) ≤ 1
    simpa using (Rat.cast_le (K := ℝ)).2 (h2.trans (by norm_num : (9/17 : ℚ) ≤ 1)))
  have hσ : 0 < σ := (by exact_mod_cast s0 : 0 < (B.lo 1 : ℝ)).trans_le hσB.1
  have hσ₁ : σ ≤ 1 / 5 := hσB.2.trans (by
    change (B.hi 1 : ℝ) ≤ 1 / 5
    simpa using (Rat.cast_le (K := ℝ)).2 s1)
  have hu : 0 ≤ u := (by exact_mod_cast u0 : 0 ≤ (B.lo 2 : ℝ)).trans huB.1
  have hu₁ : u ≤ 1 := huB.2.trans (by exact_mod_cast u1)
  have hK := k_mem hσB s1
  have hL := RatBounds.mul_mem hhB hK
  have hl : 0 < h * (σ / (2-σ)) := mul_pos hh (div_pos hσ (by linarith only [hσ₁]))
  have hl₁ : ((lBounds B).hi : ℝ) ≤ 1 := by exact_mod_cast l1
  have hM : (muBounds B w).Contains (g3Weight h σ) := G3S.weight_bounds hhB.1 hhB.2
    hσB.1 hσB.2 h0 s0.le (units_nonneg _) (units_nonneg _) wlo whi
  have hC := center_mem hL (hL.2.trans hl₁) hzB
  have hJ := jensen_sound jw hl hL.2 hl₁ hzB
  let width := (B.hi 2 : ℝ) - (B.lo 2 : ℝ)
  let θ := (u - (B.lo 2 : ℝ)) / width
  have hwidth : 0 < width := sub_pos.mpr (by exact_mod_cast uw)
  have ht₀ : 0 ≤ θ := div_nonneg (sub_nonneg.mpr huB.1) hwidth.le
  have ht₁ : θ ≤ 1 := (div_le_one₀ hwidth).2 (sub_le_sub_right huB.2 _)
  have hθ : u = (B.lo 2 : ℝ) + θ * ((B.hi 2 : ℝ) - (B.lo 2 : ℝ)) := by
    change u = (B.lo 2 : ℝ) + ((u - B.lo 2) / width) * width
    rw [div_mul_cancel₀ _ hwidth.ne']
    ring
  have hhiu : 0 ≤ B.hi 2 := u0.trans uw.le
  have hq := winner_le_gap positive hh hh₁ hσ hσ₁ hu hu₁ hz ht₀ ht₁ hθ hhB huB hzB
    hK hM hJ hC fw u0 hhiu
  have hdiv := (Quad.eval_nonneg qw ht₀ ht₁).trans hq
  simpa only [zero_mul] using (le_div_iff₀ hh).1 hdiv

theorem certTree_sound {B : Box} {t : CertTree} (positive : Bool) (ht : t.ok B positive = true)
    {h σ u z : ℝ} (hx : B.Mem ![h, σ, u, z])
    (hh : 0 < h) (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1 / 5)
    (hh₁ : h ≤ 1 / (2 - σ / (2 - σ))) (hu : 0 ≤ u) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 (signed positive u) z := by
  induction t generalizing B with
  | cone =>
    obtain ⟨hu', hz₀, hz₁⟩ := of_decide_eq_true (show decide (coneBox B) = true from ht)
    have zu₀ : (3 / 4 : ℝ) ≤ B.lo 3 := by simpa using (Rat.cast_le (K := ℝ)).2 hz₀
    have zu₁ : (B.hi 3 : ℝ) ≤ 5 / 4 := by simpa using (Rat.cast_le (K := ℝ)).2 hz₁
    have suu : (B.hi 2 : ℝ) ≤ 1 / 8 := by simpa using (Rat.cast_le (K := ℝ)).2 hu'
    have hU : (bounds B 2).Contains u := hx 2
    have hZ : (bounds B 3).Contains z := hx 3
    apply g3_equality_cone_gap hh hσ₀ hσ₁ hh₁
    · rw [signed_abs positive hu]
      exact hU.2.trans suu
    · have h₀ : 3 / 4 ≤ z := zu₀.trans hZ.1
      have h₁ : z ≤ 5 / 4 := hZ.2.trans zu₁
      rw [abs_le]
      constructor <;> linarith only [h₀, h₁]
  | empty =>
    have hs : B.hi 1 ≤ 1 / 5 ∧ 1 / (2 - G3S.kMax B) < B.lo 0 := of_decide_eq_true ht
    have hS : (bounds B 1).Contains σ := hx 1
    have hH : (bounds B 0).Contains h := hx 0
    have hhi : (B.hi 1 : ℝ) ≤ 1 / 5 := by simpa using (Rat.cast_le (K := ℝ)).2 hs.1
    have hk := (k_mem hS hs.1).2
    change σ / (2 - σ) ≤ (G3S.kMax B : ℝ) at hk
    have hk' : (G3S.kMax B : ℝ) ≤ 1 / 9 := by
      unfold G3S.kMax G3S.ratio
      push_cast
      exact (div_le_iff₀ (by linarith only [hhi] : 0 < 2 - (B.hi 1 : ℝ))).2
        (by linarith only [hhi])
    have hFalse : 1 / (2 - (G3S.kMax B : ℝ)) < (B.lo 0 : ℝ) := by
      simpa using (Rat.cast_lt (K := ℝ)).2 hs.2
    have hp := one_div_le_one_div_of_le (show 0 < 2 - (G3S.kMax B : ℝ) by
      linarith only [hk']) (sub_le_sub_left hk 2)
    exact (hFalse.not_ge (hH.1.trans (hh₁.trans hp))).elim
  | row w => exact row_sound positive ht hx hh hz
  | cut j knot lower upper ih₀ ih₁ =>
    simp only [CertTree.ok, Bool.and_eq_true] at ht
    rcases le_total (![h, σ, u, z] j) (knot : ℝ) with hb | hb
    · exact ih₀ ht.1 (Box.mem_lower hx hb)
    · exact ih₁ ht.2 (Box.mem_upper hx hb)

/-- The two sign trees on a box with complete row intervals give the actual central row. -/
theorem box_pair {h₀ h₁ σ₀ σ₁ : ℚ} {p n : CertTree}
    (hPos : p.ok ⟨![h₀, σ₀, 0, -8], ![h₁, σ₁, 1, 8]⟩ true = true)
    (hNeg : n.ok ⟨![h₀, σ₀, 0, -8], ![h₁, σ₁, 1, 8]⟩ false = true)
    {h σ s z : ℝ} (hh : 0 < h) (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1 / 5)
    (hh₁ : h ≤ 1 / (2 - σ / (2 - σ))) (hs : |s| ≤ 1) (hz : |z| ≤ 8)
    (hH₀ : (h₀ : ℝ) ≤ h) (hH₁ : h ≤ (h₁ : ℝ))
    (hS₀ : (σ₀ : ℝ) ≤ σ) (hS₁ : σ ≤ (σ₁ : ℝ)) : 0 ≤ g3FacetGap h σ 1 s z := by
  have hx : (⟨![h₀, σ₀, 0, -8], ![h₁, σ₁, 1, 8]⟩ : Box).Mem ![h, σ, |s|, z] := by
    intro i
    fin_cases i
    · exact ⟨hH₀, hH₁⟩
    · exact ⟨hS₀, hS₁⟩
    · simpa using And.intro (abs_nonneg s) hs
    · simpa using abs_le.mp hz
  rcases le_total 0 s with hsgn | hsgn
  · simpa [signed, abs_of_nonneg hsgn] using
      certTree_sound true hPos hx hh hσ₀ hσ₁ hh₁ (abs_nonneg s) hz
  · simpa [signed, abs_of_nonpos hsgn] using
      certTree_sound false hNeg hx hh hσ₀ hσ₁ hh₁ (abs_nonneg s) hz

end

end HlawkaSchatten.BelowExponent.G3P
