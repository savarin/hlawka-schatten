/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.RadicalSound
public import HlawkaSchatten.BelowExponent.VertexRegion

/-! Sound parameter-box arithmetic for the actual radicands and their certificates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

namespace RatBounds

theorem point_mem (r : ℚ) : (point r).Contains r := ⟨le_rfl, le_rfl⟩

theorem add_mem {a b : RatBounds} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := by
  simpa only [Contains, add, Rat.cast_add] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem sub_mem {a b : RatBounds} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.sub b).Contains (x-y) := by
  simpa only [Contains, sub, Rat.cast_sub] using And.intro (sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)

private theorem lower_affine {a b x y L : ℝ} (ha : a ≤ x) (hb : x ≤ b) (h₀ : L ≤ a*y)
    (h₁ : L ≤ b*y) : L ≤ x*y := by
  rcases le_total 0 y with hn | hn
  · exact h₀.trans (mul_le_mul_of_nonneg_right ha hn)
  · exact h₁.trans (mul_le_mul_of_nonpos_right hb hn)

private theorem upper_affine {a b x y U : ℝ} (ha : a ≤ x) (hb : x ≤ b) (h₀ : a*y ≤ U)
    (h₁ : b*y ≤ U) : x*y ≤ U := by
  rcases le_total 0 y with hn | hn
  · exact (mul_le_mul_of_nonneg_right hb hn).trans h₁
  · exact (mul_le_mul_of_nonpos_right ha hn).trans h₀

theorem mul_mem {a b : RatBounds} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := by
  have lo (u v : ℚ) (hu : u=a.lo ∨ u=a.hi) (hv : v=b.lo ∨ v=b.hi) :
      ((a.mul b).lo : ℝ) ≤ (u:ℝ)*v := by
    exact_mod_cast (show (a.mul b).lo ≤ u*v by
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp [mul, min_le_iff])
  have hi (u v : ℚ) (hu : u=a.lo ∨ u=a.hi) (hv : v=b.lo ∨ v=b.hi) :
      (u:ℝ)*v ≤ ((a.mul b).hi : ℝ) := by
    exact_mod_cast (show u*v ≤ (a.mul b).hi by
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp [mul, le_max_iff])
  have bounds (u : ℚ) (hu : u=a.lo ∨ u=a.hi) : (a.mul b).Contains ((u:ℝ)*y) := by
    change _ ≤ (u:ℝ)*y ∧ (u:ℝ)*y ≤ _
    rw [mul_comm (u:ℝ) y]
    constructor
    · apply lower_affine hy.1 hy.2 <;> rw [mul_comm]
      · exact lo _ _ hu (Or.inl rfl)
      · exact lo _ _ hu (Or.inr rfl)
    · apply upper_affine hy.1 hy.2 <;> rw [mul_comm]
      · exact hi _ _ hu (Or.inl rfl)
      · exact hi _ _ hu (Or.inr rfl)
  exact ⟨lower_affine hx.1 hx.2 (bounds _ (Or.inl rfl)).1 (bounds _ (Or.inr rfl)).1,
    upper_affine hx.1 hx.2 (bounds _ (Or.inl rfl)).2 (bounds _ (Or.inr rfl)).2⟩

end RatBounds

structure ParameterCell.Contains (c : ParameterCell) (a b η : ℝ) : Prop where
  first : c.a.Contains a
  second : c.b.Contains b
  eta : c.η.Contains η

private theorem depth_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a/(1+2*a) ≤ b/(1+2*b) := by
  apply (div_le_div_iff₀ (by positivity) (by linarith)).2
  linarith

theorem ParameterCell.direction_mem {c : ParameterCell} {a b η : ℝ}
    (ht : c.Contains a b η) (i : Fin 3) : (c.direction i).Contains (parameterDirection a b i) := by
  fin_cases i
  · exact ht.first
  · exact ht.second
  · have one : (RatBounds.point 1).Contains (1 : ℝ) := by simpa using RatBounds.point_mem 1
    exact RatBounds.sub_mem (RatBounds.sub_mem one ht.first) ht.second

theorem ParameterCell.radical_factors_mem {c : ParameterCell} (hη : 0 ≤ c.η.lo)
    {a b η : ℝ} (ht : c.Contains a b η) (j : Fin 3) :
    let e := parameterDirection a b
    let ε := η / (1 + 2 * η)
    (c.base j).Contains ((1 - ε) * (1 - e j) + ε * cross e j) ∧
      (c.other j).Contains (1 - ε * e j) ∧ c.sigma.Contains (sigmaTwo e) := by
  have one : (RatBounds.point 1).Contains (1:ℝ) := by simpa using RatBounds.point_mem 1
  have e (i : Fin 3) := ParameterCell.direction_mem ht i
  have he : (0 : ℝ) ≤ c.η.lo := by exact_mod_cast hη
  have hd : c.depth.Contains (η/(1+2*η)) := by
    simpa only [RatBounds.Contains, ParameterCell.depth, Rat.cast_div, Rat.cast_add,
      Rat.cast_mul, Rat.cast_one, Rat.cast_ofNat] using
      And.intro (depth_mono he ht.eta.1) (depth_mono (he.trans ht.eta.1) ht.eta.2)
  refine ⟨?_, ?_, ?_⟩
  · exact RatBounds.add_mem (RatBounds.mul_mem (RatBounds.sub_mem one hd) (RatBounds.sub_mem one (e j)))
      (RatBounds.mul_mem hd (RatBounds.mul_mem (e (j+1)) (e (j+2))))
  · exact RatBounds.sub_mem one (RatBounds.mul_mem hd (e j))
  · exact RatBounds.add_mem (RatBounds.add_mem (RatBounds.mul_mem (e 0) (e 1))
      (RatBounds.mul_mem (e 0) (e 2))) (RatBounds.mul_mem (e 1) (e 2))

theorem ParameterCell.radical_mem {c : ParameterCell} {r : Fin 3 → RatBounds}
    (hc : c.rootsOK r = true) {a b η : ℝ} (ht : c.Contains a b η) (j : Fin 3) :
    (r j).Contains (radical (η/(1+2*η)) (parameterDirection a b) j) := by
  simp only [ParameterCell.rootsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨ha, hb, hs⟩ := c.radical_factors_mem hc.1 ht j
  exact radical_mem_of_checks (hc.2 j (by simp)) ha hb hs

end HlawkaSchatten.BelowExponent.Vertex
