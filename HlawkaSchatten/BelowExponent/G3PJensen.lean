/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1Large
import all HlawkaSchatten.BelowExponent.G1
import all HlawkaSchatten.BelowExponent.G1Large
import Batteries.Tactic.OpenPrivate

/-! Monotonicity and endpoint bounds for the divided Jensen gap in G3. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set
open private absPower_convex from HlawkaSchatten.BelowExponent.G1
open private absPower_deriv from HlawkaSchatten.BelowExponent.G1Large

noncomputable section

def g3DividedJensen (l z : ℝ) : ℝ := balancedJensenGap criticalQ l 1 z / l

private theorem g3Jensen_q : 1 < criticalQ :=
  (by norm_num : (1 : ℝ) < 1054 / 665).trans criticalQ_bracket.1

/-- A larger profile depth lowers the divided Jensen gap. -/
theorem g3DividedJensen_depth {l₀ l₁ z : ℝ} (h₀ : 0 < l₀) (h : l₀ ≤ l₁) :
    g3DividedJensen l₁ z ≤ g3DividedJensen l₀ z := by
  have h₁ : 0 < l₁ := h₀.trans_le h
  let a := l₀ / l₁
  have ha₀ : 0 ≤ a := div_nonneg h₀.le h₁.le
  have ha₁ : a ≤ 1 := (div_le_one₀ h₁).2 h
  have ha : a * l₁ = l₀ := div_mul_cancel₀ _ h₁.ne'
  have hcenter : balancedFarCenter l₀ l₀ 1 z =
      (1 - a) * z + a * balancedFarCenter l₁ l₁ 1 z := by
    rw [← ha]
    simp [balancedFarCenter]
    ring
  have hc := (absPower_convex g3Jensen_q.le).2 (mem_univ z)
    (mem_univ (balancedFarCenter l₁ l₁ 1 z)) (sub_nonneg.mpr ha₁) ha₀ (sub_add_cancel 1 a)
  simp only [smul_eq_mul] at hc
  rw [← hcenter] at hc
  have hJ : a * balancedJensenGap criticalQ l₁ 1 z ≤ balancedJensenGap criticalQ l₀ 1 z := by
    simp only [balancedJensenGap, abs_one, Real.one_rpow, mul_one]
    have hp := congrArg (fun t => t * |z| ^ criticalQ) ha
    linarith only [hc, ha, hp]
  unfold g3DividedJensen
  apply (div_le_div_iff₀ h₁ h₀).2
  have hm := mul_le_mul_of_nonneg_right hJ h₁.le
  rw [show a * balancedJensenGap criticalQ l₁ 1 z * l₁ =
      (a * l₁) * balancedJensenGap criticalQ l₁ 1 z by ring, ha] at hm
  linarith only [hm]

private def absCriticalPower (x : ℝ) : ℝ := |x| ^ criticalQ

private theorem absCriticalPower_hasDeriv (x : ℝ) :
    HasDerivAt absCriticalPower (deriv absCriticalPower x) x :=
  (absPower_deriv g3Jensen_q x).differentiableAt.hasDerivAt

private theorem absCriticalPower_deriv_mono : Monotone (deriv absCriticalPower) :=
  fun _ _ h =>
    (absPower_convex g3Jensen_q.le).monotoneOn_deriv
      (fun x _ => (absCriticalPower_hasDeriv x).differentiableAt) (mem_univ _) (mem_univ _) h

private theorem g3DividedJensen_hasDeriv (l z : ℝ) :
    HasDerivAt (g3DividedJensen l)
      (((1 - l) / l) * (deriv absCriticalPower z -
        deriv absCriticalPower ((1 - l) * z + l))) z := by
  have hcenter := ((hasDerivAt_id z).const_mul (1 - l)).add_const l
  have hright := (absCriticalPower_hasDeriv ((1 - l) * z + l)).comp z hcenter
  have hleft := ((absCriticalPower_hasDeriv z).const_mul (1 - l)).add_const l
  convert (hleft.sub hright).div_const l using 1
  · funext x
    simp [g3DividedJensen, balancedJensenGap, balancedFarCenter, absCriticalPower]
  · ring

theorem g3DividedJensen_left {l : ℝ} (h₀ : 0 < l) (h₁ : l ≤ 1) :
    AntitoneOn (g3DividedJensen l) (Iic 1) := by
  refine antitoneOn_of_deriv_nonpos (convex_Iic _) ?_ ?_ ?_
  · exact (continuous_iff_continuousAt.mpr
      (fun z => (g3DividedJensen_hasDeriv l z).continuousAt)).continuousOn
  · exact fun z _ => (g3DividedJensen_hasDeriv l z).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [interior_Iic] at hz
    have hz₁ : z ≤ 1 := (mem_Iio.mp hz).le
    have hg : z ≤ (1 - l) * z + l := by
      nlinarith only [mul_nonneg h₀.le (sub_nonneg.mpr hz₁)]
    rw [(g3DividedJensen_hasDeriv l z).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (sub_nonpos.mpr (absCriticalPower_deriv_mono hg))

theorem g3DividedJensen_right {l : ℝ} (h₀ : 0 < l) (h₁ : l ≤ 1) :
    MonotoneOn (g3DividedJensen l) (Ici 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?_ ?_ ?_
  · exact (continuous_iff_continuousAt.mpr
      (fun z => (g3DividedJensen_hasDeriv l z).continuousAt)).continuousOn
  · exact fun z _ => (g3DividedJensen_hasDeriv l z).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [interior_Ici] at hz
    have hz₁ : 1 ≤ z := (mem_Ioi.mp hz).le
    have hg : (1 - l) * z + l ≤ z := by
      nlinarith only [mul_nonneg h₀.le (sub_nonneg.mpr hz₁)]
    rw [(g3DividedJensen_hasDeriv l z).deriv]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (absCriticalPower_deriv_mono hg))

/-- The mean of the right-endpoint slopes bounds the divided Jensen gap from below. -/
theorem g3DividedJensen_right_sum {l z : ℝ} (hl : 0 < l) {n : ℕ} (hn : 0 < n) :
    1 - |z| ^ criticalQ - ((1 - z) / n) *
      (∑ i ∈ Finset.range n,
        deriv (fun x : ℝ => |x| ^ criticalQ)
          (z + ((i : ℝ) + 1) * (l * (1 - z) / n))) ≤ g3DividedJensen l z := by
  let step := l * (1 - z) / (n : ℝ)
  let g (t : ℝ) := absCriticalPower (z + t * step)
  have hg : ConvexOn ℝ univ g := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul, g]
    have heq : z + (a * x + b * y) * step = a * (z + x * step) + b * (z + y * step) := by
      linear_combination -z * hab
    rw [heq]
    exact (absPower_convex g3Jensen_q.le).2 (mem_univ _) (mem_univ _) ha hb hab
  have hstep (i : ℕ) :
      g ((i : ℝ) + 1) - g i ≤
        deriv absCriticalPower (z + ((i : ℝ) + 1) * step) * step := by
    let v : ℝ := (i : ℝ) + 1
    have hd : HasDerivAt g (deriv absCriticalPower (z + v * step) * step) v := by
      have h := ((hasDerivAt_id v).mul_const step).const_add z
      simpa [g, Function.comp_def] using (absCriticalPower_hasDeriv (z + v * step)).comp v h
    have h := hg.slope_le_of_hasDerivAt (mem_univ (i : ℝ)) (mem_univ v)
      (by dsimp [v]; linarith) hd
    rwa [slope_def_field, show v - (i : ℝ) = 1 by dsimp [v]; ring, div_one] at h
  have hsum : g n - g 0 ≤ (∑ i ∈ Finset.range n,
      deriv absCriticalPower (z + ((i : ℝ) + 1) * step)) * step := by
    rw [Finset.sum_mul]
    calc
      _ = ∑ i ∈ Finset.range n, (g ((i : ℝ) + 1) - g i) := by
        symm
        simpa [Nat.cast_succ] using Finset.sum_range_sub (fun i : ℕ => g (i : ℝ)) n
      _ ≤ _ := Finset.sum_le_sum fun i _ => hstep i
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hgn : g n = absCriticalPower (balancedFarCenter l l 1 z) := by
    dsimp [g]
    congr 1
    dsimp [step]
    unfold balancedFarCenter
    field_simp
    ring
  have hg0 : g 0 = absCriticalPower z := by simp [g]
  rw [hgn, hg0] at hsum
  unfold g3DividedJensen
  apply (le_div_iff₀ hl).2
  simp only [balancedJensenGap, abs_one, Real.one_rpow, mul_one]
  let M : ℝ := ∑ i ∈ Finset.range n, deriv (fun x : ℝ => |x| ^ criticalQ)
    (z + ((i : ℝ) + 1) * (l * (1 - z) / n))
  change |balancedFarCenter l l 1 z| ^ criticalQ - |z| ^ criticalQ ≤
    M * (l * (1 - z) / n) at hsum
  change (1 - |z| ^ criticalQ - (1 - z) / n * M) * l ≤
    (1 - l) * |z| ^ criticalQ + l - |balancedFarCenter l l 1 z| ^ criticalQ
  linear_combination hsum

theorem g3DividedJensen_right_endpoint {l z : ℝ} (hl : 0 < l) :
    1 - |z| ^ criticalQ - (1 - z) * deriv (fun x : ℝ => |x| ^ criticalQ)
      (balancedFarCenter l l 1 z) ≤ g3DividedJensen l z := by
  have h := g3DividedJensen_right_sum (z := z) (n := 1) hl (by decide)
  simp only [Finset.sum_range_one, Nat.cast_zero, Nat.cast_one, zero_add, one_mul, div_one] at h
  rwa [show z + l * (1 - z) = balancedFarCenter l l 1 z by unfold balancedFarCenter; ring] at h

end

end HlawkaSchatten.BelowExponent
