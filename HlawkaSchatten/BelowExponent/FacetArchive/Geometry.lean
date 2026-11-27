/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetG2.TriangleSplit

/-! Exact facet root triangles and their ordered-strip coverage. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable section

def facetArchiveRoot (i : Fin 3) : Fin 3 → Row :=
  let a : Row := ![1/3, 1/3, 1/3]
  let b : Row := ![4/5, 1/10, 1/10]
  let c : Row := ![9/20, 9/20, 1/10]
  let d : Row := ![19/40, 19/40, 1/20]
  let e : Row := ![9/10, 1/20, 1/20]
  ![![a, b, c], ![b, c, d], ![b, d, e]] i

def FacetArchiveTriangle (q : ℝ) (v : Fin 3 → Row) : Prop :=
  ∀ {b : Row} {d : ℝ}, g2InTriangle v b → 0 ≤ d → d ≤ 1/400 → RowAt q (facetCap b d)

theorem facetArchiveTriangle_of_split {q : ℝ} {v : Fin 3 → Row} {i j : Fin 3} (hne : i ≠ j)
    (h₀ : FacetArchiveTriangle q (g2SplitTriangle v i j))
    (h₁ : FacetArchiveTriangle q (g2SplitTriangle v j i)) : FacetArchiveTriangle q v := by
  intro b d h hd₀ hd₁
  rcases g2Triangle_bisect hne h with h | h
  · exact h₀ h hd₀ hd₁
  · exact h₁ h hd₀ hd₁

theorem facetArchiveTriangle_of_weights {q : ℝ} {v : Fin 3 → Row}
    (h : ∀ (w : Row) (d : ℝ), (∀ i, 0 ≤ w i) → (∑ i, w i = 1) → 0 ≤ d → d ≤ 1/400 →
      RowAt q (facetCap (fun j => ∑ i, w i * v i j) d)) : FacetArchiveTriangle q v := by
  intro b d hb hd₀ hd₁
  obtain ⟨w, hw, hwSum, hrepr⟩ := hb
  have heq : (fun j => ∑ i, w i * v i j) = b := by
    rw [← hrepr]
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simpa only [heq] using h w d hw hwSum hd₀ hd₁

theorem facetArchiveRoot_covers {b : Row} (hsum : b 0 + b 1 + b 2 = 1)
    (hb₀ : b 1 ≤ b 0) (hb₁ : b 2 ≤ b 1) (hb₂ : 1/20 ≤ b 2) :
    ∃ i, g2InTriangle (facetArchiveRoot i) b := by
  have hupper : 2 * b 1 + b 2 ≤ 1 := by linarith only [hsum, hb₀]
  by_cases hy : 1/10 ≤ b 2
  · let a := (30/7)*(b 2-1/10)
    let c := (20/7)*(b 1-b 2)
    let w : Row := ![a, 1-a-c, c]
    refine ⟨0, w, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [w, a, c] <;> linarith only [hupper, hb₁, hy]
    · simp [Fin.sum_univ_three, w]; ring
    · funext i
      fin_cases i <;> norm_num [facetArchiveRoot, w, a, c, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Fin.sum_univ_three] <;> linarith only [hsum]
  · let u := 20*(1/10-b 2)
    have hu : 0 ≤ u := by dsimp [u]; linarith
    have hu₁ : u ≤ 1 := by dsimp [u]; linarith
    by_cases hx : (1-u)/10+(19/40)*u ≤ b 1
    · let c := (20/7)*(b 1 - ((1-u)/10+(19/40)*u))
      let w : Row := ![1-u-c, c, u]
      refine ⟨1, w, ?_, ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [w, c, u] <;> dsimp [u] at hx <;>
          linarith only [hupper, hx, hb₂, hy]
      · simp [Fin.sum_univ_three, w]
      · funext i
        fin_cases i <;> norm_num [facetArchiveRoot, w, u, c, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, Fin.sum_univ_three] <;> linarith only [hsum]
    · let d := (40/17)*(b 1-b 2)
      let w : Row := ![1-u, d, u-d]
      refine ⟨2, w, ?_, ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [w, d, u] <;> dsimp [u] at hx <;>
          linarith only [hb₁, hb₂, hx]
      · simp [Fin.sum_univ_three, w]
      · funext i
        fin_cases i <;> norm_num [facetArchiveRoot, w, u, d, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, Fin.sum_univ_three] <;> linarith only [hsum]

theorem rowAt_facetInterior_of_archive_roots {q : ℝ}
    (rows : ∀ i, FacetArchiveTriangle q (facetArchiveRoot i)) {t : Profile}
    (ht : OrderedInterior t) (hd : t 3 ≤ 1/400) (hf : 1/20 ≤ facetCoord t) : RowAt q t := by
  let b := g2FacetBase t
  have hpos : 0 < 1 - t 3 := by
    linarith only [ht.sum_four, ht.first_ge, ht.second_ge, ht.third_ge, ht.last_pos]
  have hbSum : b 0 + b 1 + b 2 = 1 := by
    simp [b, g2FacetBase, Fin.castSucc, ← add_div, div_eq_iff hpos.ne']
    linarith only [ht.sum_four]
  have hb₀ : b 1 ≤ b 0 := div_le_div_of_nonneg_right ht.first_ge hpos.le
  have hb₁ : b 2 ≤ b 1 := div_le_div_of_nonneg_right ht.second_ge hpos.le
  have hb₂ : 1/20 ≤ b 2 := hf
  obtain ⟨i, hi⟩ := facetArchiveRoot_covers hbSum hb₀ hb₁ hb₂
  rw [← g2_facetCap_base ht]
  exact rows i hi ht.last_pos.le hd

end

end HlawkaSchatten.BelowExponent
