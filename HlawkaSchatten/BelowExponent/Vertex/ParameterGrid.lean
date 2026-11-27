/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.ParameterBounds
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck

/-! Closed rational subdivisions of the three parameter intervals. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

namespace RatBounds

private theorem knot_first (r : RatBounds) (n : ℕ) : r.knot n 0 = r.lo := by simp [knot]

private theorem knot_last (r : RatBounds) {n : ℕ} (hn : 0 < n) : r.knot n n = r.hi := by
  unfold knot
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn']
  ring

private theorem adjacent_interval (f : ℕ → ℝ) (x : ℝ) (h₀ : f 0 ≤ x) (n : ℕ) (hn : x ≤ f (n+1)) :
    ∃ i ≤ n, f i ≤ x ∧ x ≤ f (i+1) := by
  induction n with
  | zero => exact ⟨0, le_rfl, h₀, hn⟩
  | succ n ih =>
      rcases le_total x (f (n+1)) with h | h
      · obtain ⟨i, hi, hlo, hhi⟩ := ih h
        exact ⟨i, hi.trans (Nat.le_succ n), hlo, hhi⟩
      · exact ⟨n+1, le_rfl, h, hn⟩

theorem subinterval_cover {r : RatBounds} {x : ℝ} (h : r.Contains x) {n : ℕ} (hn : 0 < n) :
    ∃ i : Fin n, (r.subinterval n i.val).Contains x := by
  cases n with
  | zero => omega
  | succ n =>
      let f (i : ℕ) := (r.knot (n+1) i : ℝ)
      have hf₀ : f 0 ≤ x := by simpa only [f, knot_first] using h.1
      have hf₁ : x ≤ f (n+1) := by simpa only [f, knot_last r hn] using h.2
      obtain ⟨i, hi, hlo, hhi⟩ := adjacent_interval f x hf₀ n hf₁
      exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, hlo, hhi⟩

end RatBounds

namespace ParameterCell

theorem grid_cover {c : ParameterCell} {a b η : ℝ} (h : c.Contains a b η)
    {na nb nη : ℕ} (ha : 0 < na) (hb : 0 < nb) (hη : 0 < nη) :
    ∃ d ∈ c.grid na nb nη, d.Contains a b η := by
  obtain ⟨i, hi⟩ := RatBounds.subinterval_cover h.first ha
  obtain ⟨j, hj⟩ := RatBounds.subinterval_cover h.second hb
  obtain ⟨k, hk⟩ := RatBounds.subinterval_cover h.eta hη
  refine ⟨⟨_, _, _⟩, ?_, ⟨hi, hj, hk⟩⟩
  exact List.mem_flatMap.mpr ⟨i, by simp, List.mem_flatMap.mpr ⟨j, by simp, List.mem_map.mpr ⟨k, by simp, rfl⟩⟩⟩

end ParameterCell

end HlawkaSchatten.BelowExponent.Vertex
