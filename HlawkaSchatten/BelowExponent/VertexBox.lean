/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.VertexFeature
public import HlawkaSchatten.BelowExponent.BulkGeometry
import all HlawkaSchatten.BelowExponent.Interpolation
import Batteries.Tactic.OpenPrivate

/-! The eight vertex inequalities and the three directional curvature budgets imply the real gap. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

open Set
open private abs_rpow_lerp_le from HlawkaSchatten.BelowExponent.Interpolation

def LowerChord (f : ℝ → ℝ) (a b loss : ℝ) : Prop :=
  ∀ u ∈ Icc 0 1, interpolate u (f a) (f b) - loss ≤ f (interpolate u a b)

/-- The affine argument may vanish or change sign inside the interval. -/
theorem gap_chord_of_coefficients {q a b M : ℝ} (hq : 1 < q) (hab : a ≤ b) (hM : 0 ≤ M)
    (z : Row) {d d' d'' : ℝ → Row} {h h' h'' : ℝ → Fin 3 → Row} {L : ℝ → ℝ}
    (hc : ContinuousOn (fun t => linearFeature q (d t) (h t) z) (Icc a b))
    (hd : ∀ t ∈ interior (Icc a b), ∀ i, HasDerivAt (fun v => d v i) (d' t i) t)
    (hh : ∀ t ∈ interior (Icc a b), ∀ i j, HasDerivAt (fun v => h v i j) (h' t i j) t)
    (hdd : ∀ t ∈ interior (Icc a b), ∀ i, HasDerivAt (fun v => d' v i) (d'' t i) t)
    (hhh : ∀ t ∈ interior (Icc a b), ∀ i j, HasDerivAt (fun v => h' v i j) (h'' t i j) t)
    (hK : ∀ t ∈ interior (Icc a b), ∃ K : Row, (∀ i, curvatureBudget q (d'' t) (h'' t) i ≤ K i) ∧
      ∑ i, K i * |z i|^q ≤ M)
    (hL : ∀ u ∈ Icc 0 1, L (interpolate u a b) = interpolate u (L a) (L b)) :
    LowerChord (fun t => linearFeature q (d t) (h t) z - |L t|^q) a b (M*(b-a)^2/8) := by
  intro u hu
  have hf := vertex_chord_of_second_le hab hu hM hc
    (fun t ht => hasDerivAt_linearFeature q t z (hd t ht) (hh t ht))
    (fun t ht => hasDerivAt_linearFeature q t z (hdd t ht) (hhh t ht))
    (fun t ht => by
      obtain ⟨K, hbudget, hsum⟩ := hK t ht
      exact (linearFeature_le_budget hq hbudget z).trans hsum)
  have hp := abs_rpow_lerp_le hq.le hu.1 hu.2 (L a) (L b)
  dsimp only
  rw [hL u hu]
  unfold interpolate
  linarith only [hf, hp]

private theorem lower_bound_at {f : ℝ → ℝ} {a b u loss B : ℝ}
    (hf : LowerChord f a b loss) (hu : u ∈ Icc 0 1)
    (ha : B+loss ≤ f a) (hb : B+loss ≤ f b) : B ≤ f (interpolate u a b) := by
  have h := hf u hu
  unfold interpolate at h ⊢
  linarith only [h, mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hu.2), mul_le_mul_of_nonneg_left hb hu.1]

private theorem interpolate_mem {w a b : ℝ} (hw : w ∈ Icc 0 1) (hab : a ≤ b) :
    interpolate w a b ∈ Icc a b := by
  unfold interpolate
  constructor <;> nlinarith only [mul_nonneg hw.1 (sub_nonneg.mpr hab),
    mul_nonneg (sub_nonneg.mpr hw.2) (sub_nonneg.mpr hab)]

/-- The parent error is paid exactly once per axis. The margins may depend on the row z. -/
theorem gap_of_eight_corners {lo hi w K : Row} (hb : ∀ i, lo i ≤ hi i)
    (hw : ∀ i, w i ∈ Icc 0 1) (gap : ℝ → ℝ → ℝ → ℝ)
    (hx : ∀ y ∈ Icc (lo 1) (hi 1), ∀ z ∈ Icc (lo 2) (hi 2),
      LowerChord (fun x => gap x y z) (lo 0) (hi 0) (K 0))
    (hy : ∀ i : Bool, ∀ z ∈ Icc (lo 2) (hi 2),
      LowerChord (fun y => gap (chooseCorner i (lo 0) (hi 0)) y z) (lo 1) (hi 1) (K 1))
    (hz : ∀ i j : Bool, LowerChord (gap (chooseCorner i (lo 0) (hi 0))
      (chooseCorner j (lo 1) (hi 1))) (lo 2) (hi 2) (K 2))
    (hc : ∀ i j k : Bool, K 0+K 1+K 2 ≤ gap (chooseCorner i (lo 0) (hi 0))
      (chooseCorner j (lo 1) (hi 1)) (chooseCorner k (lo 2) (hi 2))) :
    0 ≤ gap (interpolate (w 0) (lo 0) (hi 0)) (interpolate (w 1) (lo 1) (hi 1))
      (interpolate (w 2) (lo 2) (hi 2)) := by
  let coord (i : Fin 3) := interpolate (w i) (lo i) (hi i)
  have hm (i : Fin 3) : coord i ∈ Icc (lo i) (hi i) := interpolate_mem (hw i) (hb i)
  have hface (i j : Bool) : K 0+K 1 ≤
      gap (chooseCorner i (lo 0) (hi 0)) (chooseCorner j (lo 1) (hi 1)) (coord 2) :=
    lower_bound_at (hz i j) (hw 2) (hc i j false) (hc i j true)
  have hedge (i : Bool) : K 0 ≤ gap (chooseCorner i (lo 0) (hi 0)) (coord 1) (coord 2) :=
    lower_bound_at (f := fun y => gap (chooseCorner i (lo 0) (hi 0)) y (coord 2))
      (hy i _ (hm 2)) (hw 1) (hface i false) (hface i true)
  exact lower_bound_at (f := fun x => gap x (coord 1) (coord 2)) (hx _ (hm 1) _ (hm 2)) (hw 0)
    (by simpa [chooseCorner] using hedge false) (by simpa [chooseCorner] using hedge true)

/-- The three parameter slices of the concrete coefficient test have separately affine arguments. -/
def parameterArgument (z : Row) (a b η : ℝ) := argument η ![a,b,1-a-b] z

theorem parameterArgument_affine (z : Row) (a b η lo hi u : ℝ) :
    parameterArgument z (interpolate u lo hi) b η =
      interpolate u (parameterArgument z lo b η) (parameterArgument z hi b η) ∧
    parameterArgument z a (interpolate u lo hi) η =
      interpolate u (parameterArgument z a lo η) (parameterArgument z a hi η) ∧
    parameterArgument z a b (interpolate u lo hi) =
      interpolate u (parameterArgument z a b lo) (parameterArgument z a b hi) := by
  simp [parameterArgument, argument, linearRow, interpolate, Fin.sum_univ_three]
  exact ⟨by ring, by ring, by ring⟩

end HlawkaSchatten.BelowExponent.Vertex
