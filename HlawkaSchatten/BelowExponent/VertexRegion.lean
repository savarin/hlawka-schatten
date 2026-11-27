/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.VertexBox

/-! Vertex certificate inputs in their three actual parameter coordinates (a,b,η). -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

open Set

noncomputable section

def parameterDirection (a b : ℝ) : Row := ![a,b,1-a-b]

def parameterD (a b η : ℝ) : Row :=
  let e := parameterDirection a b
  let ε := η/(1+2*η)
  coefficient ε (betaHeavy η e) e (beta η e) (radical ε e)

def parameterWeight (a b η : ℝ) : Row :=
  rowWeight η (radical (η/(1+2*η)) (parameterDirection a b)) (parameterD a b η)

def parameterGap (q : ℝ) (z : Row) (a b η : ℝ) : ℝ :=
  let e := parameterDirection a b
  feature q η e (radical (η/(1+2*η)) e) (parameterD a b η) z - |parameterArgument z a b η| ^ q

theorem parameterGap_eq_linear (q : ℝ) (z : Row) (a b η : ℝ) :
    parameterGap q z a b η = linearFeature q (parameterD a b η)
      (fun i j => (1-parameterDirection a b i)*parameterWeight a b η j) z -
      |parameterArgument z a b η|^q := by
  exact congrArg (fun x : ℝ => x - |parameterArgument z a b η|^q) (feature_eq_linear _ _ _ _ _ _)

/-- This form also admits a separate proof on side-cone rows. -/
theorem rowAt_of_parameter_rows {q : ℝ} {t : Profile} (hq : 1 < q) (ht : OrderedInterior t)
    (hsmall : vertexDepth t < 1/2)
    (checked : let e := directions t; let η := vertexDepth t/(1-2*vertexDepth t)
      (∀ j, 0 ≤ parameterWeight (e 0) (e 1) η j) ∧ (∀ z, 0 ≤ parameterGap q z (e 0) (e 1) η)) :
    RowAt q t := by
  let e := directions t
  let ε := vertexDepth t
  let η := ε/(1-2*ε)
  have hηden : 0 < 1-2*ε := by dsimp [ε]; linarith only [hsmall]
  have hη : 0 < η := div_pos ht.depth_pos hηden
  have hh : η * (1-2*ε) = ε := div_mul_cancel₀ _ hηden.ne'
  have heps : η/(1+2*η) = ε := (div_eq_iff (show 1+2*η ≠ 0 by positivity)).2 (by linarith only [hh])
  have hsum : e 0+e 1+e 2=1 := by simpa only [e, Fin.sum_univ_three] using directions_sum ht
  have he : parameterDirection (e 0) (e 1) = e := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · change 1-e 0-e 1=e 2
      linarith only [hsum]
  have harg (z : Row) : parameterArgument z (e 0) (e 1) η = argument η e z :=
    congrArg (fun v => argument η v z) he
  apply rowAt_of_coefficient_checks hq ht hsmall
  change (∀ j, 0 ≤ parameterWeight (e 0) (e 1) η j) ∧ (∀ z, 0 ≤ parameterGap q z (e 0) (e 1) η)
    at checked
  constructor
  · simpa only [parameterWeight, parameterD, heps, he] using checked.1
  · intro z
    have hc := checked.2 z
    simp only [parameterGap, parameterD, harg, heps, he, sub_nonneg] at hc
    exact hc

/-- The eight corner margins and the three curvature losses for one real row. -/
structure BoxChecks (q : ℝ) (z lo hi K : Row) : Prop where
  ordered : ∀ i, lo i ≤ hi i
  first : ∀ b ∈ Icc (lo 1) (hi 1), ∀ η ∈ Icc (lo 2) (hi 2),
    LowerChord (fun a => parameterGap q z a b η) (lo 0) (hi 0) (K 0)
  second : ∀ i : Bool, ∀ η ∈ Icc (lo 2) (hi 2),
    LowerChord (fun b => parameterGap q z (chooseCorner i (lo 0) (hi 0)) b η) (lo 1) (hi 1) (K 1)
  third : ∀ i j : Bool, LowerChord
    (parameterGap q z (chooseCorner i (lo 0) (hi 0)) (chooseCorner j (lo 1) (hi 1)))
    (lo 2) (hi 2) (K 2)
  corners : ∀ i j k : Bool, K 0+K 1+K 2 ≤ parameterGap q z (chooseCorner i (lo 0) (hi 0))
    (chooseCorner j (lo 1) (hi 1)) (chooseCorner k (lo 2) (hi 2))

/-- The same checked parameter corner can serve any incident cell whose three
coordinate losses it pays. A side-cone restriction stays attached to the row. -/
theorem corners_of_shared_margins {q : ℝ} {lo hi loss needed z : Row}
    {stored : Bool → Bool → Bool → Row} {applies : Row → Prop} (hz : applies z)
    (hpay : loss 0 + loss 1 + loss 2 ≤ ∑ m, needed m * |z m| ^ q)
    (hbudget : ∀ i j k m, needed m ≤ stored i j k m)
    (hrecord : ∀ i j k x, applies x → ∑ m, stored i j k m * |x m| ^ q ≤
      parameterGap q x (chooseCorner i (lo 0) (hi 0))
        (chooseCorner j (lo 1) (hi 1)) (chooseCorner k (lo 2) (hi 2))) :
    ∀ i j k, loss 0 + loss 1 + loss 2 ≤ parameterGap q z
      (chooseCorner i (lo 0) (hi 0)) (chooseCorner j (lo 1) (hi 1))
      (chooseCorner k (lo 2) (hi 2)) := by
  intro i j k
  exact hpay.trans ((Finset.sum_le_sum fun m _ =>
    mul_le_mul_of_nonneg_right (hbudget i j k m) (Real.rpow_nonneg (abs_nonneg _) _)).trans
    (hrecord i j k z hz))

theorem parameterGap_of_box {q : ℝ} {z lo hi w K : Row}
    (hc : BoxChecks q z lo hi K) (hw : ∀ i, w i ∈ Icc 0 1) :
    0 ≤ parameterGap q z (interpolate (w 0) (lo 0) (hi 0)) (interpolate (w 1) (lo 1) (hi 1))
      (interpolate (w 2) (lo 2) (hi 2)) :=
  gap_of_eight_corners hc.ordered hw (parameterGap q z) hc.first hc.second hc.third hc.corners

/-- All original rows at a point of a vertex box verified by its coefficient test. -/
theorem rowAt_of_vertex_box {q : ℝ} {t : Profile} (hq : 1 < q) (ht : OrderedInterior t)
    (hsmall : vertexDepth t < 1/2) {lo hi w : Row} (hw : ∀ i, w i ∈ Icc 0 1)
    (ha : directions t 0 = interpolate (w 0) (lo 0) (hi 0))
    (hb : directions t 1 = interpolate (w 1) (lo 1) (hi 1))
    (hη : vertexDepth t/(1-2*vertexDepth t) = interpolate (w 2) (lo 2) (hi 2))
    (hweight : ∀ j, 0 ≤ parameterWeight (directions t 0) (directions t 1)
      (vertexDepth t/(1-2*vertexDepth t)) j)
    (hrows : ∀ z : Row, ∃ K : Row, BoxChecks q z lo hi K) : RowAt q t := by
  apply rowAt_of_parameter_rows hq ht hsmall
  refine ⟨hweight, fun z => ?_⟩
  obtain ⟨K, hc⟩ := hrows z
  simpa only [ha, hb, hη] using (parameterGap_of_box hc hw)

end
end HlawkaSchatten.BelowExponent.Vertex
