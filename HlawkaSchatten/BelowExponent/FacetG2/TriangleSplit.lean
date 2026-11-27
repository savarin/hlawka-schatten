/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.Geometry

/-! The midpoint split used by the exact G2 facet tree. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable section

def g2InTriangle (v : Fin 3 → Row) (b : Row) : Prop :=
  ∃ w : Row, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∑ i, w i • v i) = b

def g2SplitTriangle (v : Fin 3 → Row) (i j : Fin 3) : Fin 3 → Row :=
  Function.update v i ((1 / 2 : ℝ) • (v i + v j))

private theorem g2_move_to_midpoint {v : Fin 3 → Row} {b w : Row} {i j : Fin 3} (hne : i ≠ j)
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1) (hrepr : (∑ k, w k • v k) = b)
    (hij : w i ≤ w j) : g2InTriangle (g2SplitTriangle v i j) b := by
  let after : Row := fun k => if k = i then 2 * w i else if k = j then w j - w i else w k
  refine ⟨after, ?_, ?_, ?_⟩
  · intro k
    by_cases hki : k = i
    · simp [after, hki, hw]
    by_cases hkj : k = j
    · subst k
      simp [after, Ne.symm hne, sub_nonneg.mpr hij]
    · simp [after, hki, hkj, hw]
  · calc
      ∑ k, after k = ∑ k, w k := by
        fin_cases i <;> fin_cases j <;> norm_num at hne
        all_goals (norm_num [after, Fin.sum_univ_three]; ring)
      _ = 1 := hsum
  · rw [← hrepr]
    funext s
    fin_cases i <;> fin_cases j <;> norm_num at hne
    all_goals
      (norm_num [after, g2SplitTriangle, Function.update, Fin.sum_univ_three,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul]
       ring)

theorem g2Triangle_bisect {v : Fin 3 → Row} {b : Row} {i j : Fin 3} (hne : i ≠ j)
    (hb : g2InTriangle v b) :
    g2InTriangle (g2SplitTriangle v i j) b ∨ g2InTriangle (g2SplitTriangle v j i) b := by
  obtain ⟨w, hnonneg, hsum, hrepr⟩ := hb
  rcases le_total (w i) (w j) with h | h
  · exact Or.inl (g2_move_to_midpoint hne hnonneg hsum hrepr h)
  · exact Or.inr (g2_move_to_midpoint (Ne.symm hne) hnonneg hsum hrepr h)

def G2TriangleRows (q : ℝ) (v : Fin 3 → Row) : Prop :=
  ∀ {b : Row} {d : ℝ}, g2InTriangle v b → 0 ≤ d → d ≤ 1 / 500 → RowAt q (facetCap b d)

theorem g2TriangleRows_of_bisect {q : ℝ} {v : Fin 3 → Row} {i j : Fin 3} (hne : i ≠ j)
    (hl : G2TriangleRows q (g2SplitTriangle v i j))
    (hr : G2TriangleRows q (g2SplitTriangle v j i)) : G2TriangleRows q v := by
  intro b d hb hd₀ hd
  rcases g2Triangle_bisect hne hb with h | h
  · exact hl h hd₀ hd
  · exact hr h hd₀ hd

theorem g2TriangleRows_of_weights {q : ℝ} {v : Fin 3 → Row}
    (rows : ∀ (w : Row) (d : ℝ), (∀ i, 0 ≤ w i) → (∑ i, w i = 1) →
      0 ≤ d → d ≤ 1 / 500 → RowAt q (facetCap (fun j => ∑ i, w i * v i j) d)) :
    G2TriangleRows q v := by
  intro b d hb hd₀ hd
  obtain ⟨w, hw, hs, heq⟩ := hb
  have hfun : (fun j => ∑ i, w i * v i j) = b := by
    funext j
    rw [← heq]
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simpa only [hfun] using rows w d hw hs hd₀ hd

theorem rowAt_g2Band_of_triangleRoots {q : ℝ}
    (rows : ∀ upper side, G2TriangleRows q (g2SliceRoot upper side))
    {b : Row} {d : ℝ} (hb : G2FacetBand b) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt q (facetCap b d) := by
  obtain ⟨upper, side, w, hp, hs, hrepr⟩ := g2SliceRoot_covers hb
  exact rows upper side ⟨w, hp, hs, hrepr⟩ hd₀ hd

end

end HlawkaSchatten.BelowExponent
