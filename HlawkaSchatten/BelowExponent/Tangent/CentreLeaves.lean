/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.Real

/-! The strict cube test at profile vertices excludes an entire centre leaf. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Tangent

private theorem cubeCoordinate {x d n m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (h : (if d ≤ 4 * x then 4 * x - d else d - 4 * x) * m < 4 * d * n) :
    |(x : ℝ) / d - 1 / 4| < (n : ℝ) / m := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have he : (x : ℝ) / d - 1 / 4 = (4 * x - d) / (4 * d) := by
    field_simp
  rw [he, abs_div, abs_of_pos (mul_pos (by norm_num) hd')]
  apply (div_lt_div_iff₀ (mul_pos (by norm_num) hd') hm').2
  by_cases hx : d ≤ 4 * x
  · rw [ite_eq_left hx] at h
    have hr : (d : ℝ) ≤ 4 * (x : ℝ) := by exact_mod_cast hx
    rw [abs_of_nonneg (sub_nonneg.mpr hr)]
    have hc : (((4 * x - d : ℕ) : ℝ) * m) < 4 * (d : ℝ) * n := by exact_mod_cast h
    rw [Nat.cast_sub hx] at hc
    push_cast at hc
    nlinarith only [hc]
  · rw [ite_eq_right hx] at h
    have hr : 4 * (x : ℝ) ≤ d := by exact_mod_cast (le_of_not_ge hx : 4 * x ≤ d)
    rw [abs_of_nonpos (sub_nonpos.mpr hr)]
    have hc : (((d - 4 * x : ℕ) : ℝ) * m) < 4 * (d : ℝ) * n := by exact_mod_cast h
    rw [Nat.cast_sub (le_of_not_ge hx)] at hc
    push_cast at hc
    nlinarith only [hc]

private theorem convex_center_cube (r : ℝ) :
    Convex ℝ {u : Profile | ∀ i, |u i - 1 / 4| < r} := by
  intro u hu v hv a b ha hb hab i
  change |a * u i + b * v i - 1 / 4| < r
  have he : a * u i + b * v i - 1 / 4 = a * (u i - 1 / 4) + b * (v i - 1 / 4) := by
    linarith only [hab]
  rw [he]
  apply lt_of_le_of_lt (abs_add_le _ _)
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  rcases ha.eq_or_lt with rfl | hpos
  · obtain rfl : b = 1 := by simpa using hab
    simpa using hv i
  · calc
      _ < a * r + b * r := add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left (hu i) hpos) (mul_le_mul_of_nonneg_left (hv i).le hb)
      _ = _ := by rw [← add_mul, hab, one_mul]

/-- Every point of an accepted centre leaf lies strictly inside the certified cube. -/
theorem inside_of_inCube {H : TC.Hdr} {G : TC.Geom}
    (hm : 0 < H.rcD) (hd : 0 < (TC.cellVerts G).2) (hc : TC.inCube H G = true)
    {t : Profile} (ht : t ∈ cellSet G) (i : Fin 4) :
    |t i - 1 / 4| < (H.rcN : ℝ) / H.rcD := by
  apply (convexHull_min (t := {u : Profile | ∀ i, |u i - 1 / 4| < (H.rcN : ℝ) / H.rcD})
    _ (convex_center_cube _) ht) i
  rintro _ ⟨v, hv, rfl⟩ j
  unfold TC.inCube at hc
  generalize hg : TC.cellVerts G = vd at hd hc hv ⊢
  obtain ⟨vertices, den⟩ := vd
  dsimp only at hc hd hv ⊢
  have h := List.all_eq_true.mp hc v hv
  simp only [Bool.and_eq_true, TC.blt_true] at h
  fin_cases j
  · exact cubeCoordinate hd hm h.1.1.1
  · exact cubeCoordinate hd hm h.1.1.2
  · exact cubeCoordinate hd hm h.1.2
  · exact cubeCoordinate hd hm h.2

end HlawkaSchatten.BelowExponent.Tangent
