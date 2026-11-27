/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.Sound
public import HlawkaSchatten.BelowExponent.AdaptiveCoverage
public import HlawkaSchatten.BelowExponent.Interpolation
import all HlawkaSchatten.BelowExponent.Exponents
import Batteries.Tactic.OpenPrivate

/-! Real weights and convex interpolation for the fine tangent certificate. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Tangent

open private rational_lt_criticalQ criticalQ_lt_rational from HlawkaSchatten.BelowExponent.Exponents

/-- Positive denominators turn the two integer tests into a strict exponent bracket. -/
theorem exponent_bracket_of_tabOK {P : TC.Prof} {T : TC.Tab} (hT : TC.tabOK P T = true)
    (hk : 0 < P.k1 ∧ 0 < P.k2) :
    (P.n1 : ℝ) / P.k1 < criticalQ ∧ criticalQ < (P.n2 : ℝ) / P.k2 := by
  have h := TC.tabOK_spec P T hT
  exact ⟨rational_lt_criticalQ P.n1 P.k1 hk.1 h.1, criticalQ_lt_rational P.n2 P.k2 hk.2 h.2.1⟩

noncomputable def profileWeight (H : TC.Hdr) (D : TC.CellData) (s : Fin 4) : ℝ :=
  (D.p.getD s.val 0 : ℝ) / H.Dw

noncomputable def rowWeight (H : TC.Hdr) (D : TC.CellData) (j : Fin 3) : ℝ :=
  (D.g.getD j.val 0 : ℝ) / H.Dw

/-- The normalization and budget on the certificate's integer weights give the real budgets. -/
theorem weights_of_cellOK {H : TC.Hdr} {G : TC.Geom} {D : TC.CellData}
    (h : TC.cellOK H G D = true) :
    IsSimplex (profileWeight H D) ∧ (∀ j, 0 ≤ rowWeight H D j) ∧ ∑ j, rowWeight H D j ≤ 1 := by
  obtain ⟨p₀, p₁, p₂, p₃, g₀, g₁, g₂, hp, hg, hDen, hP, hG, _⟩ := TC.cellOK_spec H G D h
  have hd : 0 < (H.Dw : ℝ) := by exact_mod_cast hDen
  have hs : (p₀ : ℝ) + p₁ + p₂ + p₃ = H.Dw := by exact_mod_cast hP
  have hb : (g₀ : ℝ) + g₁ + g₂ ≤ H.Dw := by exact_mod_cast hG
  refine ⟨⟨fun _ => div_nonneg (Nat.cast_nonneg _) hd.le, ?_⟩,
    fun _ => div_nonneg (Nat.cast_nonneg _) hd.le, ?_⟩
  · simp [Fin.sum_univ_four, profileWeight, hp, ← add_div, hs, hd.ne']
  · simpa [Fin.sum_univ_three, rowWeight, hg, ← add_div, div_le_one₀ hd] using hb

noncomputable def vertex (den : ℕ) (v : TC.V4) : Profile :=
  ![(v.v0 : ℝ) / den, (v.v1 : ℝ) / den, (v.v2 : ℝ) / den, (v.v3 : ℝ) / den]

noncomputable def cellSet (G : TC.Geom) : Set Profile :=
  convexHull ℝ {t | ∃ v ∈ (TC.cellVerts G).1, t = vertex (TC.cellVerts G).2 v}

/-- Every real face coordinate in a checked integer rectangle belongs to a passing leaf,
including coordinates on either side's common split line. -/
theorem exists_leaf_at {P : ℕ → ℕ → ℕ → ℕ → Prop} {a₀ a₁ b₀ b₁ : ℕ}
    (cover : TC.BoxCover P a₀ a₁ b₀ b₁) {a b : ℝ}
    (ha : a ∈ Set.Icc (a₀ : ℝ) a₁) (hb : b ∈ Set.Icc (b₀ : ℝ) b₁) :
    ∃ l r u v : ℕ, P l r u v ∧ a ∈ Set.Icc (l : ℝ) r ∧ b ∈ Set.Icc (u : ℝ) v := by
  induction cover with
  | leaf h => exact ⟨_, _, _, _, h, ha, hb⟩
  | splitA m _ _ _ _ ih₀ ih₁ =>
    rcases le_total a (m : ℝ) with h | h
    · exact ih₀ ⟨ha.1, h⟩ hb
    · exact ih₁ ⟨h, ha.2⟩ hb
  | splitB m _ _ _ _ ih₀ ih₁ =>
    rcases le_total b (m : ℝ) with h | h
    · exact ih₀ ha ⟨hb.1, h⟩
    · exact ih₁ ha ⟨h, hb.2⟩

/-- At fixed row and weights the valid profiles form a convex set. -/
theorem convex_weightedRow {q : ℝ} (hq : 1 ≤ q) {π : Profile} (hπ : ∀ s, 0 ≤ π s)
    (γ x : Row) : Convex ℝ {t : Profile | WeightedRow q t π γ x} := by
  intro t₀ h₀ t₁ h₁ a b ha hb hab
  change ∑ s, π s * |rowEval (a • t₀ + b • t₁) s x| ^ q ≤ _
  calc
    _ ≤ ∑ s, π s * (a * |rowEval t₀ s x| ^ q + b * |rowEval t₁ s x| ^ q) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left ((convexOn_abs_rowEval_rpow hq s x).2
        (Set.mem_univ t₀) (Set.mem_univ t₁) ha hb hab) (hπ s)
    _ = a * (∑ s, π s * |rowEval t₀ s x| ^ q) + b * (∑ s, π s * |rowEval t₁ s x| ^ q) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ a * (∑ j, γ j * |x j| ^ q) + b * (∑ j, γ j * |x j| ^ q) :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ ha) (mul_le_mul_of_nonneg_left h₁ hb)
    _ = _ := by rw [← add_mul, hab, one_mul]

/-- A passing cell needs the real row estimate only at its computed vertices. -/
theorem rowAt_of_cell_vertices {H : TC.Hdr} {G : TC.Geom} {D : TC.CellData}
    (h : TC.cellOK H G D = true) {q : ℝ} (hq : 1 ≤ q)
    (hv : ∀ v ∈ (TC.cellVerts G).1, ∀ x,
      WeightedRow q (vertex (TC.cellVerts G).2 v) (profileWeight H D) (rowWeight H D) x)
    {t : Profile} (ht : t ∈ cellSet G) : RowAt q t := by
  obtain ⟨hπ, hγ, hsum⟩ := weights_of_cellOK h
  refine ⟨profileWeight H D, hπ, rowWeight H D, hγ, hsum, fun x => ?_⟩
  apply convexHull_min (t := {u : Profile | WeightedRow q u (profileWeight H D) (rowWeight H D) x})
    _ (convex_weightedRow hq hπ.1 _ _) ht
  rintro _ ⟨v, hv', rfl⟩
  exact hv v hv' x

end HlawkaSchatten.BelowExponent.Tangent
