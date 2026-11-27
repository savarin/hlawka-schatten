/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PData
public import HlawkaSchatten.BelowExponent.G3Cone
import Mathlib.Tactic

/-! Soundness of adaptive box joins and quadratic signs in the final G3 chart. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

noncomputable section

def Box.Mem (B : Box) (x : Fin 4 → ℝ) : Prop :=
  ∀ j, (B.lo j : ℝ) ≤ x j ∧ x j ≤ (B.hi j : ℝ)

def Quad.eval (p : Quad) (u : ℝ) : ℝ :=
  ((p.a : ℝ) * u ^ 2 + (p.b : ℝ) * u + (p.c : ℝ)) / p.scale

theorem Quad.eval_nonneg {p : Quad} (hp : p.ok = true) {u : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) : 0 ≤ p.eval u := by
  unfold Quad.ok at hp
  obtain ⟨hscale, hc, hend, hinterior⟩ := of_decide_eq_true hp
  have hcr : (0 : ℝ) ≤ p.c := by exact_mod_cast hc
  have her : (0 : ℝ) ≤ (p.a : ℝ) + p.b + p.c := by exact_mod_cast hend
  let a : ℝ := p.a
  let b : ℝ := p.b
  let c : ℝ := p.c
  have bound : 0 ≤ a * u ^ 2 + b * u + c := by
    change 0 ≤ c at hcr
    change 0 ≤ a + b + c at her
    by_cases ha : 0 < a
    · by_cases hb : 0 ≤ b
      · positivity
      · by_cases hb' : b ≤ -2 * a
        · have hmul : 0 ≤ (u - 1) * (a * (u + 1) + b) := by
            have h := mul_le_mul_of_nonneg_left (show u + 1 ≤ 2 by linarith) ha.le
            exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
          linarith only [hmul, her]
        · have haZ : 0 < p.a := by
            exact_mod_cast (show (0 : ℝ) < (p.a : ℝ) from ha)
          have hbZ : p.b < 0 := by
            exact_mod_cast (show (p.b : ℝ) < 0 from lt_of_not_ge hb)
          have hloZ : -2 * p.a < p.b := by
            exact_mod_cast (show -2 * (p.a : ℝ) < (p.b : ℝ) from lt_of_not_ge hb')
          have hdisc := hinterior ⟨haZ, hloZ, hbZ⟩
          have hr : 0 ≤ 4 * a * c - b ^ 2 := by
            have h := (Int.cast_le (R := ℝ)).2 hdisc
            push_cast at h
            exact h
          have hprod : 0 ≤ 4 * a * (a * u ^ 2 + b * u + c) := by
            linarith only [sq_nonneg (2 * a * u + b), hr]
          exact nonneg_of_mul_nonneg_right hprod (by positivity)
    · have hmul := mul_nonneg (mul_nonneg (neg_nonneg.mpr (le_of_not_gt ha)) hu₀)
        (sub_nonneg.mpr hu₁)
      have htail := mul_nonneg hu₀ her
      have hfirst := mul_nonneg (sub_nonneg.mpr hu₁) hcr
      linarith only [hmul, htail, hfirst]
  exact div_nonneg bound (by exact_mod_cast hscale.le)

def signed (positive : Bool) (u : ℝ) : ℝ := if positive then u else -u

/-- Every exported numeric leaf provides its own real lower bound for the divided gap. -/
def LeafBounds (positive : Bool) (tree : Tree) (B : Box) : Prop :=
  ∀ (C : Box) (q : Quad), (C, q) ∈ tree.numericLeaves B →
    ∀ x, C.Mem x → 0 < x 0 →
      q.eval ((x 2 - C.lo 2) / ((C.hi 2 : ℝ) - C.lo 2)) ≤
        g3FacetGap (x 0) (x 1) 1 (signed positive (x 2)) (x 3) / x 0

theorem Box.mem_lower {B : Box} {x : Fin 4 → ℝ} (hx : B.Mem x)
    {j : Fin 4} {m : ℚ} (h : x j ≤ (m : ℝ)) : (B.lowerChild j m).Mem x := by
  intro k
  by_cases hk : k = j
  · subst k
    exact ⟨(hx j).1, by simpa [Box.lowerChild] using h⟩
  · simpa [Box.lowerChild, hk] using hx k

theorem Box.mem_upper {B : Box} {x : Fin 4 → ℝ} (hx : B.Mem x)
    {j : Fin 4} {m : ℚ} (h : (m : ℝ) ≤ x j) : (B.upperChild j m).Mem x := by
  intro k
  by_cases hk : k = j
  · subst k
    exact ⟨by simpa [Box.upperChild] using h, (hx j).2⟩
  · simpa [Box.upperChild, hk] using hx k

theorem gap_of_tree (positive : Bool) (tree : Tree) (B : Box)
    (hok : tree.ok B = true) (hb : LeafBounds positive tree B)
    {x : Fin 4 → ℝ} (hx : B.Mem x) (hu : 0 ≤ x 2)
    (hh : 0 < x 0) (hσ : 0 < x 1) (hσ₁ : x 1 ≤ 1 / 5)
    (hh₁ : x 0 ≤ 1 / (2 - x 1 / (2 - x 1))) :
    0 ≤ g3FacetGap (x 0) (x 1) 1 (signed positive (x 2)) (x 3) := by
  induction tree generalizing B with
  | cone =>
    have hc : coneBox B := of_decide_eq_true hok
    obtain ⟨hu₁, hz₀, hz₁⟩ := hc
    have huR := (Rat.cast_le (K := ℝ)).2 hu₁
    have hzlR := (Rat.cast_le (K := ℝ)).2 hz₀
    have hzhR := (Rat.cast_le (K := ℝ)).2 hz₁
    norm_num at huR hzlR hzhR
    have hsu : x 2 ≤ 1 / 8 := (hx 2).2.trans huR
    have hzl : 3 / 4 ≤ x 3 := hzlR.trans (hx 3).1
    have hzh : x 3 ≤ 5 / 4 := (hx 3).2.trans hzhR
    apply g3_equality_cone_gap hh hσ hσ₁ hh₁
    · cases positive <;> simpa [signed, abs_of_nonneg hu] using hsu
    · rw [abs_le]
      exact ⟨by linarith, by linarith⟩
  | box q =>
    simp only [Tree.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hwidth : 0 < (B.hi 2 : ℝ) - B.lo 2 :=
      sub_pos.mpr (by exact_mod_cast hok.1)
    have hu₀ := div_nonneg (sub_nonneg.mpr (hx 2).1) hwidth.le
    have hu₁ := (div_le_one₀ hwidth).mpr (sub_le_sub_right (hx 2).2 _)
    have hq := Quad.eval_nonneg hok.2 hu₀ hu₁
    have hl := hb B q (by simp [Tree.numericLeaves]) x hx hh
    simpa only [zero_mul] using (le_div_iff₀ hh).mp (hq.trans hl)
  | cut j m lower upper ihLower ihUpper =>
    simp only [Tree.ok, Bool.and_eq_true, and_assoc] at hok
    rcases le_total (x j) (m : ℝ) with h | h
    · apply ihLower (B.lowerChild j m) hok.2.1 _ (Box.mem_lower hx h)
      intro C q hC
      exact hb C q (by simp [Tree.numericLeaves, hC])
    · apply ihUpper (B.upperChild j m) hok.2.2 _ (Box.mem_upper hx h)
      intro C q hC
      exact hb C q (by simp [Tree.numericLeaves, hC])

theorem chart_of_box_trees (B : Box) (negative positive : Tree)
    (hn : negative.ok B = true) (hp : positive.ok B = true)
    (hnb : LeafBounds false negative B) (hpb : LeafBounds true positive B)
    {h σ s z : ℝ} (hx : B.Mem ![h, σ, |s|, z])
    (hh : 0 < h) (hσ : 0 < σ) (hσ₁ : σ ≤ 1 / 5)
    (hh₁ : h ≤ 1 / (2 - σ / (2 - σ))) : 0 ≤ g3FacetGap h σ 1 s z := by
  rcases le_total 0 s with hs₀ | hs₀
  · simpa [signed, abs_of_nonneg hs₀] using
      gap_of_tree true positive B hp hpb hx (abs_nonneg s) hh hσ hσ₁ hh₁
  · simpa [signed, abs_of_nonpos hs₀] using
      gap_of_tree false negative B hn hnb hx (abs_nonneg s) hh hσ hσ₁ hh₁

/-- Exact cover of the full normalized \(p=1\) chart from two adaptive trees. -/
theorem full_chart_of_trees (negative positive : Tree)
    (hn : negative.ok root = true) (hp : positive.ok root = true)
    (hnb : LeafBounds false negative root) (hpb : LeafBounds true positive root)
    {h σ s z : ℝ} (hh : 0 < h) (hσ₀ : 7 / 10000 ≤ σ) (hσ₁ : σ ≤ 1 / 5)
    (hh₁ : h ≤ 1 / (2 - σ / (2 - σ))) (hs : |s| ≤ 1) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 s z := by
  let x : Fin 4 → ℝ := ![h, σ, |s|, z]
  have hhmax := (g3_h_max hσ₁ hh₁).trans (by norm_num : (9 : ℝ)/17 ≤ 17/32)
  have hx : root.Mem x := by
    intro j
    fin_cases j
    · simpa [root, x] using And.intro hh.le hhmax
    · simpa [root, x] using And.intro hσ₀ hσ₁
    · simpa [root, x] using And.intro (abs_nonneg s) hs
    · simpa [root, x] using abs_le.mp hz
  have hσ : 0 < σ := (by norm_num : (0 : ℝ) < 7 / 10000).trans_le hσ₀
  exact chart_of_box_trees root negative positive hn hp hnb hpb hx hh hσ hσ₁ hh₁

end

end HlawkaSchatten.BelowExponent.G3P
