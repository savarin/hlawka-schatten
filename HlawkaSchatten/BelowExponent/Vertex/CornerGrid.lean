/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CornerGridData
public import HlawkaSchatten.BelowExponent.Vertex.CornerRectangle
public import HlawkaSchatten.BelowExponent.Vertex.CornerRows
import all HlawkaSchatten.BelowExponent.Vertex.CurvatureSound
import all HlawkaSchatten.BelowExponent.Vertex.SideConeGrid
import Batteries.Tactic.OpenPrivate

/-! The closed chart cover transfers the checked row rectangles to all required rows. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

open Set
open private interpolate_exists from HlawkaSchatten.BelowExponent.Vertex.CurvatureSound
open private sideRowInterval_cover from HlawkaSchatten.BelowExponent.Vertex.SideConeGrid

noncomputable section

private theorem outerInterval_rat (i : Fin 34) :
    (outerInterval i).lo < (outerInterval i).hi ∧
      (0 ≤ (outerInterval i).lo ∨ (outerInterval i).hi ≤ 0) := by
  have h : (List.finRange 34).all (fun i => decide ((outerInterval i).lo < (outerInterval i).hi ∧
      (0 ≤ (outerInterval i).lo ∨ (outerInterval i).hi ≤ 0))) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

private theorem outerInterval_cover {x : ℝ} (hx : |x| ≤ 1) :
    ∃ i : Fin 34, (outerInterval i).Contains x := by
  have h₀ : (outerNodes.get 0 : ℝ) ≤ x := by
    simpa only [show outerNodes.get 0 = -1 by decide +kernel, Rat.cast_neg, Rat.cast_one] using
      (abs_le.mp hx).1
  have h₁ : x ≤ (outerNodes.get (Fin.last 34) : ℝ) := by
    simpa only [show outerNodes.get (Fin.last 34) = 1 by decide +kernel, Rat.cast_one] using
      (abs_le.mp hx).2
  obtain ⟨i, hi, _⟩ := sideRowInterval_cover outerNodes x h₀ h₁ (by decide +kernel)
  exact ⟨i, hi⟩

private theorem cast_outerChartRow (k : Fin 3) (u v : ℚ) (d : Fin 3) :
    ((outerChartRow k u v d : ℚ) : ℝ) = outerFaceRow k (u : ℝ) (v : ℝ) d := by
  fin_cases k <;> fin_cases d <;> simp [outerChartRow, outerFaceRow]

private theorem chosenEndpoint (i : Fin 34) (x : Bool) :
    (outerEndpoint (outerInterval i) x : ℝ) =
      chooseCorner x ((outerInterval i).lo : ℝ) ((outerInterval i).hi : ℝ) := by
  cases x <;> rfl

/-- A closed Grid B rectangle at one parameter corner. -/
def OuterRectangleAt (margins : Fin 3 → ℚ) (a b η : ℝ) (k : Fin 3) (i j : Fin 34) : Prop :=
  ∀ ⦃u v : ℝ⦄, (outerInterval i).Contains u → (outerInterval j).Contains v →
    CornerMarginAt margins (outerFaceRow k u v) a b η

theorem outerRectangle_of_endpoint_bounds {margins : Fin 3 → ℚ} {a b η : ℝ}
    (k : Fin 3) (i j : Fin 34) {du dv : ℝ} {cu cv : Bool → ℝ} :
    let U := outerInterval i
    let V := outerInterval j
    let D := cornerRowCoefficients margins a b η
    du ≤ D.diagonal (outerFaceFirst k) → dv ≤ D.diagonal (outerFaceSecond k) →
    (∀ y, if (0 : ℝ) ≤ U.lo then cu y ≤ D.firstCoeff k (outerEndpoint V y)
      else D.firstCoeff k (outerEndpoint V y) ≤ cu y) →
    (∀ x, if (0 : ℝ) ≤ V.lo then cv x ≤ D.secondCoeff k (outerEndpoint U x)
      else D.secondCoeff k (outerEndpoint U x) ≤ cv x) →
    (∀ x y, 0 ≤ D.remainder criticalQ k (outerEndpoint U x) (outerEndpoint V y) +
      cornerAxisMinorant criticalQ du (cu y) U.lo U.hi x +
      cornerAxisMinorant criticalQ dv (cv x) V.lo V.hi y) → OuterRectangleAt margins a b η k i j := by
  dsimp only
  intro hdu hdv hcu hcv hcorner u v hu hv
  have hw (l : Fin 34) : ((outerInterval l).lo : ℝ) < (outerInterval l).hi := by
    exact_mod_cast (outerInterval_rat l).1
  have hs (l : Fin 34) : (0 : ℝ) ≤ (outerInterval l).lo ∨ ((outerInterval l).hi : ℝ) ≤ 0 := by
    rcases (outerInterval_rat l).2 with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  rw [show (outerInterval i).Contains u = (u ∈ Icc ((outerInterval i).lo : ℝ)
    ((outerInterval i).hi : ℝ)) from rfl] at hu
  rw [show (outerInterval j).Contains v = (v ∈ Icc ((outerInterval j).lo : ℝ)
    ((outerInterval j).hi : ℝ)) from rfl] at hv
  exact cornerMargin_of_rectangle k hu hv (hw i) (hw j) (hs i) (hs j) hdu hdv
    (by simpa only [chosenEndpoint] using hcu) (by simpa only [chosenEndpoint] using hcv)
    (by simpa only [chosenEndpoint] using hcorner)

private theorem outerLinear_on_rectangle (k : Fin 3) (i j : Fin 34)
    {u v : ℝ} (hu : (outerInterval i).Contains u) (hv : (outerInterval j).Contains v)
    (s : ℝ) (c : Row) (P : ℝ → Prop)
    (hinterp : ∀ ⦃t x y⦄, t ∈ Icc (0 : ℝ) 1 → P x → P y → P (interpolate t x y))
    (hcorner : ∀ x y, P (s * outerLinear c (outerFaceRow k (outerEndpoint (outerInterval i) x)
      (outerEndpoint (outerInterval j) y)))) :
    P (s * outerLinear c (outerFaceRow k u v)) := by
  obtain ⟨α, hα, rfl⟩ := interpolate_exists hu
  obtain ⟨β, hβ, rfl⟩ := interpolate_exists hv
  let f := fun x y : ℝ => s * outerLinear c (outerFaceRow k x y)
  let U := outerInterval i
  let V := outerInterval j
  have h (x y) : P (f (outerEndpoint U x) (outerEndpoint V y)) := hcorner x y
  have hl := hinterp hβ (h false false) (h false true)
  have hr := hinterp hβ (h true false) (h true true)
  have hs := hinterp hα hl hr
  simp only [outerEndpoint, Bool.false_eq_true, ite_false, ite_true] at hs
  convert hs using 1
  fin_cases k <;> simp [f, outerLinear, outerFaceRow, interpolate] <;> ring

theorem outerSideSkip_sound {k : Fin 3} {i j : Fin 34} {u v : ℝ}
    (hskip : outerSideSkip k i j = true) (hu : (outerInterval i).Contains u)
    (hv : (outerInterval j).Contains v) : InSideNearCone (outerFaceRow k u v) := by
  let U := outerInterval i
  let V := outerInterval j
  let s := outerSideSign k U V
  have hs (x y : Bool) : let z := outerChartRow k (outerEndpoint U x) (outerEndpoint V y)
      0 < s*z 0 ∧ ∀ d : Fin 5, 0 ≤ s * outerLinear (fun n => (sideConeNormal d n : ℚ)) z := by
    have hx : x ∈ [false,true] := by cases x <;> decide
    have hy : y ∈ [false,true] := by cases y <;> decide
    have hh := List.all_eq_true.mp (List.all_eq_true.mp hskip x hx) y hy
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hh
    exact ⟨hh.1, fun d => hh.2 d (List.mem_finRange d)⟩
  let z := outerFaceRow k u v
  have hp : 0 < (s : ℝ)*z 0 := by
    have h := outerLinear_on_rectangle k i j hu hv (s : ℝ) ![1,0,0] (fun x => 0 < x)
      (fun {t _ _} ht hx hy => by
        obtain he | hpos := ht.1.eq_or_lt
        · simpa [interpolate, ← he] using hx
        · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) hx.le) (mul_pos hpos hy))
    have hfirst (row : Row) : outerLinear (![1,0,0] : Row) row = row 0 := by simp [outerLinear]
    simp only [hfirst] at h
    apply h
    intro x y
    have hh : (0 : ℝ) < ((s * outerChartRow k (outerEndpoint U x) (outerEndpoint V y) 0 : ℚ) : ℝ) := by
      exact_mod_cast (hs x y).1
    simpa only [Rat.cast_mul, cast_outerChartRow] using hh
  have hh (d : Fin 5) : 0 ≤ (s : ℝ)*outerLinear (fun n => (sideConeNormal d n : ℝ)) z := by
    apply outerLinear_on_rectangle k i j hu hv (s : ℝ) _ (fun x => 0 ≤ x)
    · exact fun {_ _ _} ht hx hy => add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hx) (mul_nonneg ht.1 hy)
    · intro x y
      have h : (0 : ℝ) ≤ ((s * outerLinear (fun n => (sideConeNormal d n : ℚ))
        (outerChartRow k (outerEndpoint U x) (outerEndpoint V y)) : ℚ) : ℝ) := by
        exact_mod_cast (hs x y).2 d
      simp only [outerLinear, Rat.cast_mul, Rat.cast_add, Rat.cast_intCast] at h ⊢
      rw [cast_outerChartRow, cast_outerChartRow, cast_outerChartRow] at h
      exact h
  have hz₀ : z 0 ≠ 0 := right_ne_zero_of_mul hp.ne'
  let x := -z 1/z 0-1
  let y := -z 2/z 0-1
  have hx : x*((s : ℝ)*z 0) = (s : ℝ)*(-z 1-z 0) := by
    dsimp only [x]
    field_simp [hz₀]
  have hy : y*((s : ℝ)*z 0) = (s : ℝ)*(-z 2-z 0) := by
    dsimp only [y]
    field_simp [hz₀]
  change z 0 ≠ 0 ∧ -5/8 ≤ x ∧ x ≤ 2 ∧ -3/4 ≤ y ∧ y ≤ 3 ∧ -5/8 ≤ x+y
  refine ⟨hz₀, (mul_le_mul_iff_left₀ hp).mp ?_, (mul_le_mul_iff_left₀ hp).mp ?_,
    (mul_le_mul_iff_left₀ hp).mp ?_, (mul_le_mul_iff_left₀ hp).mp ?_, (mul_le_mul_iff_left₀ hp).mp ?_⟩
  · rw [hx]
    have h := hh 0
    norm_num [sideConeNormal, outerLinear] at h
    nlinarith only [h]
  · rw [hx]
    have h := hh 1
    norm_num [sideConeNormal, outerLinear] at h
    nlinarith only [h]
  · rw [hy]
    have h := hh 2
    norm_num [sideConeNormal, outerLinear] at h
    nlinarith only [h]
  · rw [hy]
    have h := hh 3
    norm_num [sideConeNormal, outerLinear] at h
    nlinarith only [h]
  · rw [add_mul, hx, hy]
    have h := hh 4
    norm_num [sideConeNormal, outerLinear] at h
    nlinarith only [h]

private theorem outerFaceRow_eq {k : Fin 3} {z : Row} (hk : z k = 1) :
    outerFaceRow k (z (outerFaceFirst k)) (z (outerFaceSecond k)) = z := by
  funext l
  fin_cases k <;> fin_cases l <;> simp [outerFaceRow, outerFaceFirst, outerFaceSecond] <;> exact hk.symm

theorem cornerMargin_of_vc_grid {margins : Fin 3 → ℚ} {a b η : ℝ}
    (h : ∀ k i j, OuterRectangleAt margins a b η k i j) (z : Row) : CornerMarginAt margins z a b η := by
  apply cornerMargin_of_charts (applies := fun _ => True) (fun _ _ => trivial) _ z trivial
  intro k row hk he _
  obtain ⟨i, hi⟩ := outerInterval_cover (he (outerFaceFirst k))
  obtain ⟨j, hj⟩ := outerInterval_cover (he (outerFaceSecond k))
  simpa only [outerFaceRow_eq hk] using h k i j hi hj

theorem cornerMargin_of_sc_grid {margins : Fin 3 → ℚ} {a b η : ℝ}
    (h : ∀ k i j, outerSideSkip k i j = false → OuterRectangleAt margins a b η k i j)
    (z : Row) (hz : ¬ InSideNearCone z) : CornerMarginAt margins z a b η := by
  apply cornerMargin_of_charts (applies := fun v => ¬ InSideNearCone v)
    (fun hρ hg hscaled => hg ((inSideNearCone_scale_iff hρ _).mp hscaled)) _ z hz
  intro k row hk he houter
  obtain ⟨i, hi⟩ := outerInterval_cover (he (outerFaceFirst k))
  obtain ⟨j, hj⟩ := outerInterval_cover (he (outerFaceSecond k))
  have hkeep : outerSideSkip k i j = false := by
    cases hh : outerSideSkip k i j
    · rfl
    · exact (houter (outerFaceRow_eq hk ▸ outerSideSkip_sound hh hi hj)).elim
  simpa only [outerFaceRow_eq hk] using h k i j hkeep hi hj

end

end HlawkaSchatten.BelowExponent.Vertex
