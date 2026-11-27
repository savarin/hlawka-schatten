/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureGrid

/-! The coefficient bounds pay for the three real chords of a vertex cell. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

open Set

namespace ParameterCell

noncomputable def lower (c : ParameterCell) : Row := fun k => (c.coordinate k).lo
noncomputable def upper (c : ParameterCell) : Row := fun k => (c.coordinate k).hi

theorem contains_iff {c : ParameterCell} (p : Row) : c.Contains (p 0) (p 1) (p 2) ↔
    ∀ k, p k ∈ Icc (c.lower k) (c.upper k) := by
  constructor
  · intro h k
    fin_cases k
    · exact h.first
    · exact h.second
    · exact h.eta
  · exact fun h => ⟨h 0, h 1, h 2⟩

/-- The strict base bounds give two derivatives even on the closed faces of the cell. -/
def jetDomainOK (c : ParameterCell) : Bool :=
  decide (0 ≤ c.η.lo ∧ 0 < (c.direction 1).lo ∧ 0 < (c.direction 2).lo ∧ 0 < c.sigma.lo) &&
  (List.finRange 3).all fun i => decide (0 < (c.base i).lo ∧ 0 < (c.other i).lo)

noncomputable def axisLoss (c : ParameterCell) (caps : Fin 3 → Fin 3 → ℚ) (z : Row) (k : Fin 3) : ℝ :=
  (∑ i, (caps k i : ℝ) * |z i| ^ criticalQ) * (c.upper k - c.lower k)^2 / 8

theorem axisLoss_sum (c : ParameterCell) (caps : Fin 3 → Fin 3 → ℚ) (z : Row) :
    c.axisLoss caps z 0 + c.axisLoss caps z 1 + c.axisLoss caps z 2 =
      ∑ i, (curvatureLoss c caps i : ℝ) * |z i| ^ criticalQ := by
  simp only [axisLoss, curvatureLoss, Fin.sum_univ_three, Rat.cast_add, Rat.cast_div, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_sub, Rat.cast_ofNat, lower, upper]
  ring

private theorem axis_chord {c : ParameterCell} {caps : Fin 3 → Fin 3 → ℚ}
    (hdom : c.jetDomainOK = true) (hn : ∀ k i, 0 ≤ caps k i) (k : Fin 3) (z p : Row)
    (hab : c.lower k ≤ c.upper k) (hp : ∀ i, i ≠ k → p i ∈ Icc (c.lower i) (c.upper i))
    (hcap : ∀ v : Row, c.Contains (v 0) (v 1) (v 2) → ∀ j,
      curvatureBudget criticalQ (fun i => (parameterDJet k v i).second)
        (fun i l => (parameterHJet k v i l).second) j ≤ (caps k j : ℝ)) :
    LowerChord (fun x => let v := axisPoint p k x; parameterGap criticalQ z (v 0) (v 1) (v 2))
      (c.lower k) (c.upper k) (c.axisLoss caps z k) := by
  let point := axisPoint p k
  have hmem (x : ℝ) (hx : x ∈ Icc (c.lower k) (c.upper k)) :
      c.Contains (point x 0) (point x 1) (point x 2) := by
    apply (contains_iff _).2
    intro i
    by_cases hi : i = k
    · subst i
      simpa only [point, axisPoint, Function.update_self] using hx
    · simpa only [point, axisPoint, Function.update_of_ne hi] using hp i hi
  simp only [jetDomainOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hdom
  have hpos (i : Fin 3) := hdom.2 i (by simp)
  let d (x : ℝ) (i : Fin 3) := parameterDJet k (point x) i
  let h (x : ℝ) (i j : Fin 3) := parameterHJet k (point x) i j
  have valid (x : ℝ) (hx : x ∈ Icc (c.lower k) (c.upper k)) :
      (∀ i, Jet.ValidAt (fun t => d t i) x) ∧ (∀ i j, Jet.ValidAt (fun t => h t i j) x) := by
    have he : ![point x 0, point x 1, point x 2] = point x := by
      funext i
      fin_cases i <;> rfl
    have hv := ParameterCell.coefficientJets_valid (hmem x hx) k hdom.1.1 hdom.1.2.1 hdom.1.2.2.1
      (fun i => (hpos i).1) (fun i => (hpos i).2) hdom.1.2.2.2
    dsimp only at hv
    rw [he] at hv
    simpa only [d, h, point, axisPoint, Function.update_self, Function.update_idem] using hv
  let L (x : ℝ) := parameterArgument z (point x 0) (point x 1) (point x 2)
  have hL (u : ℝ) (_ : u ∈ Icc 0 1) : L (interpolate u (c.lower k) (c.upper k)) =
      interpolate u (L (c.lower k)) (L (c.upper k)) := by
    have ha := parameterArgument_affine z (p 0) (p 1) (p 2) (c.lower k) (c.upper k) u
    fin_cases k
    · simpa [L, point, axisPoint, Function.update_apply] using ha.1
    · simpa [L, point, axisPoint, Function.update_apply] using ha.2.1
    · simpa [L, point, axisPoint, Function.update_apply] using ha.2.2
  have hq : 1 < criticalQ := by linarith [criticalQ_bracket.1]
  have hM : 0 ≤ ∑ i, (caps k i : ℝ) * |z i| ^ criticalQ := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (by exact_mod_cast hn k i)
      (Real.rpow_nonneg (abs_nonneg _) _)
  have hi (x : ℝ) (hx : x ∈ interior (Icc (c.lower k) (c.upper k))) :=
    valid x (interior_subset hx)
  have hc : ContinuousOn (fun x => linearFeature criticalQ (fun i => (d x i).value)
      (fun i j => (h x i j).value) z) (Icc (c.lower k) (c.upper k)) := by
    intro x hx
    exact (hasDerivAt_linearFeature criticalQ x z (fun i => ((valid x hx).1 i).1)
      (fun i j => ((valid x hx).2 i j).1)).continuousAt.continuousWithinAt
  have hg := gap_chord_of_coefficients hq hab hM z hc (fun x hx i => ((hi x hx).1 i).1)
    (fun x hx i j => ((hi x hx).2 i j).1) (fun x hx i => ((hi x hx).1 i).2)
    (fun x hx i j => ((hi x hx).2 i j).2) (fun x hx =>
      ⟨fun i => (caps k i : ℝ), hcap (point x) (hmem x (interior_subset hx)), le_rfl⟩) hL
  simpa only [axisLoss, L, d, h, parameterGap_eq_linear, parameterDJet_value, parameterHJet_value] using hg

private theorem corner_mem {a b : ℝ} (h : a ≤ b) (i : Bool) : chooseCorner i a b ∈ Icc a b := by
  cases i
  · exact ⟨le_rfl, h⟩
  · exact ⟨h, le_rfl⟩

/-- Checked grid caps and margins at the eight corners close the cell for a fixed row. -/
theorem boxChecks_of_curvature {c : ParameterCell} {caps : Fin 3 → Fin 3 → ℚ} (z : Row)
    (hdom : c.jetDomainOK = true) (hn : ∀ k i, 0 ≤ caps k i)
    (hab : ∀ k, c.lower k ≤ c.upper k)
    (hcap : ∀ v : Row, c.Contains (v 0) (v 1) (v 2) → ∀ k j,
      curvatureBudget criticalQ (fun i => (parameterDJet k v i).second)
        (fun i l => (parameterHJet k v i l).second) j ≤ (caps k j : ℝ))
    (hcorner : ∀ i j k : Bool, (∑ m, (curvatureLoss c caps m : ℝ) * |z m| ^ criticalQ) ≤
      parameterGap criticalQ z (chooseCorner i (c.lower 0) (c.upper 0))
        (chooseCorner j (c.lower 1) (c.upper 1)) (chooseCorner k (c.lower 2) (c.upper 2))) :
    BoxChecks criticalQ z c.lower c.upper (c.axisLoss caps z) := by
  have hx (k : Fin 3) (p : Row) := c.axis_chord hdom hn k z p (hab k) (hcap := fun v hv => hcap v hv k)
  refine ⟨hab, ?_, ?_, ?_, ?_⟩
  · intro b hb η hη
    have hv := hx 0 ![0,b,η] (by
      intro i hi
      fin_cases i
      · exact False.elim (hi rfl)
      · exact hb
      · exact hη)
    simpa [axisPoint, Function.update_apply] using hv
  · intro i η hη
    have hv := hx 1 ![chooseCorner i (c.lower 0) (c.upper 0),0,η] (by
      intro j hj
      fin_cases j
      · exact corner_mem (hab 0) i
      · exact False.elim (hj rfl)
      · exact hη)
    simpa [axisPoint, Function.update_apply] using hv
  · intro i j
    have hv := hx 2 ![chooseCorner i (c.lower 0) (c.upper 0),chooseCorner j (c.lower 1) (c.upper 1),0] (by
      intro k hk
      fin_cases k
      · exact corner_mem (hab 0) i
      · exact corner_mem (hab 1) j
      · exact False.elim (hk rfl))
    simpa [axisPoint, Function.update_apply] using hv
  · rw [axisLoss_sum]
    exact hcorner

private theorem interpolate_exists {a b x : ℝ} (hx : x ∈ Icc a b) :
    ∃ w ∈ Icc (0 : ℝ) 1, interpolate w a b = x := by
  rcases eq_or_lt_of_le (hx.1.trans hx.2) with hab | hab
  · exact ⟨0, by simp, by simpa [interpolate] using le_antisymm hx.1 (hx.2.trans_eq hab.symm)⟩
  · refine ⟨(x-a)/(b-a), ⟨div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hab.le), ?_⟩, ?_⟩
    · exact (div_le_one (sub_pos.mpr hab)).2 (sub_le_sub_right hx.2 a)
    · unfold interpolate
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      ring

theorem parameterGap_of_cell {c : ParameterCell} {z : Row} {a b η : ℝ} {loss : Row}
    (hc : BoxChecks criticalQ z c.lower c.upper loss) (ht : c.Contains a b η) :
    0 ≤ parameterGap criticalQ z a b η := by
  obtain ⟨u, hu, he₀⟩ := interpolate_exists ht.first
  obtain ⟨v, hv, he₁⟩ := interpolate_exists ht.second
  obtain ⟨w, hw, he₂⟩ := interpolate_exists ht.eta
  have h := parameterGap_of_box (w := ![u,v,w]) hc (by
    intro i
    fin_cases i
    · exact hu
    · exact hv
    · exact hw)
  change 0 ≤ parameterGap criticalQ z
    (interpolate u (c.a.lo : ℝ) c.a.hi) (interpolate v (c.b.lo : ℝ) c.b.hi)
    (interpolate w (c.η.lo : ℝ) c.η.hi) at h
  rwa [he₀, he₁, he₂] at h

/-- All points of a checked grid inherit any row inequality that pays its eight corner margins. -/
theorem parameterGap_of_curvature_grid {c : ParameterCell} {roots : Fin 3 → RatBounds}
    {na nb nη : ℕ} {caps : Fin 3 → Fin 3 → ℚ} {weightFloor : ℚ} {needed : Fin 3 → ℚ}
    {a b η : ℝ} {z : Row}
    (ht : c.Contains a b η) (ha : 0 < na) (hb : 0 < nb) (hη : 0 < nη)
    (hroot : c.rootsOK roots = true) (hcheck : gridCurvatureOK c roots na nb nη caps weightFloor = true)
    (hdom : c.jetDomainOK = true) (hn : ∀ k i, 0 ≤ caps k i)
    (hpaid : ∀ i, curvatureLoss c caps i ≤ needed i)
    (hcorner : ∀ i j k : Bool, (∑ m, (needed m : ℝ) * |z m| ^ criticalQ) ≤
      parameterGap criticalQ z (chooseCorner i (c.lower 0) (c.upper 0))
        (chooseCorner j (c.lower 1) (c.upper 1)) (chooseCorner k (c.lower 2) (c.upper 2))) :
    0 ≤ parameterGap criticalQ z a b η := by
  have hm := (contains_iff (c := c) ![a,b,η]).1 ht
  have hordered (k : Fin 3) := (hm k).1.trans (hm k).2
  have hmargin : (∑ m, (curvatureLoss c caps m : ℝ) * |z m| ^ criticalQ) ≤
      ∑ m, (needed m : ℝ) * |z m| ^ criticalQ :=
    Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hpaid m)
      (Real.rpow_nonneg (abs_nonneg _) _)
  exact parameterGap_of_cell (boxChecks_of_curvature z hdom hn hordered (fun _ hv =>
    (gridCurvatureOK_sound hv ha hb hη hroot hcheck).2) (fun i j k => hmargin.trans (hcorner i j k))) ht

end ParameterCell

end HlawkaSchatten.BelowExponent.Vertex
