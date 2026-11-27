/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Bulk
public import HlawkaSchatten.BelowExponent.BulkGeometry

/-! Soundness of signed nonuniform row grids. An integer corner test is
sufficient when the lower input table interpolates below the power. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable section

/-- Signed row coordinates and lower input ordinates at a common scale. -/
structure BulkRowGrid (n : ℕ) where
  coordDen : ℕ
  valueDen : ℕ
  coordinate : Fin (n + 2) → ℤ
  input : Fin (n + 2) → ℤ

namespace BulkRowGrid

variable {n : ℕ}

def point (g : BulkRowGrid n) (i : Fin (n + 2)) : ℝ :=
  (g.coordinate i : ℝ) / g.coordDen

def lower (g : BulkRowGrid n) (i : Fin (n + 2)) : ℝ :=
  (g.input i : ℝ) / g.valueDen

structure Sound (g : BulkRowGrid n) (q : ℝ) : Prop where
  coordDen_pos : 0 < g.coordDen
  valueDen_pos : 0 < g.valueDen
  first : g.point 0 = -1
  last : g.point (Fin.last (n + 1)) = 1
  lower_lerp : ∀ (i : Fin (n + 1)) {w : ℝ}, w ∈ Set.Icc 0 1 →
    (1 - w) * g.lower i.castSucc + w * g.lower i.succ ≤
      |(1 - w) * g.point i.castSucc + w * g.point i.succ| ^ q

def chart {α : Type*} (k : Fin 3) (d a b : α) : Fin 3 → α :=
  ![![d, a, b], ![a, d, b], ![a, b, d]] k

private theorem chart_map {α β : Type*} (f : α → β) (k : Fin 3) (d a b : α) (j : Fin 3) :
    f (chart k d a b j) = chart k (f d) (f a) (f b) j := by
  fin_cases k <;> fin_cases j <;> rfl

/-- Signed integer coordinates of a corner on the chart with coordinate `k` fixed. -/
def cornerCoords (g : BulkRowGrid n) (k : Fin 3) (a b : Fin (n + 2)) : Fin 3 → ℤ :=
  chart k g.coordDen (g.coordinate a) (g.coordinate b)

def cornerRow (g : BulkRowGrid n) (k : Fin 3) (a b : Fin (n + 2)) : Row :=
  fun j => (g.cornerCoords k a b j : ℝ) / g.coordDen

def cornerLower (g : BulkRowGrid n) (k : Fin 3) (a b : Fin (n + 2)) : Fin 3 → ℤ :=
  chart k g.valueDen (g.input a) (g.input b)

private theorem cornerRow_chart {g : BulkRowGrid n} {q : ℝ} (hg : g.Sound q)
    (k : Fin 3) (a b : Fin (n + 2)) :
    g.cornerRow k a b = chart k 1 (g.point a) (g.point b) := by
  have hDen : 0 < (g.coordDen : ℝ) := by exact_mod_cast hg.coordDen_pos
  funext j
  simp only [cornerRow, cornerCoords, chart_map (fun x : ℤ => (x : ℝ) / g.coordDen),
    Int.cast_natCast, div_self hDen.ne', point]

private theorem cornerLower_chart {g : BulkRowGrid n} {q : ℝ} (hg : g.Sound q)
    (k : Fin 3) (a b : Fin (n + 2)) (j : Fin 3) :
    (g.cornerLower k a b j : ℝ) / g.valueDen = chart k 1 (g.lower a) (g.lower b) j := by
  have hDen : 0 < (g.valueDen : ℝ) := by exact_mod_cast hg.valueDen_pos
  simp only [cornerLower, chart_map (fun x : ℤ => (x : ℝ) / g.valueDen),
    Int.cast_natCast, div_self hDen.ne', lower]

private def rowFactor (w : ℝ) (b : Bool) : ℝ := if b then w else 1 - w

private def rowWeight (u v : ℝ) (b : Bool × Bool) : ℝ := rowFactor u b.1 * rowFactor v b.2

private theorem rowFactor_nonneg {w : ℝ} (hw : w ∈ Set.Icc 0 1) (b : Bool) :
    0 ≤ rowFactor w b := by
  cases b
  · exact sub_nonneg.mpr hw.2
  · exact hw.1

private theorem sum_rowWeight (u v : ℝ) : ∑ b, rowWeight u v b = 1 := by
  simp [Fintype.sum_prod_type, rowWeight, rowFactor]
  ring

private def adjacent (i : Fin (n + 1)) (flag : Bool) : Fin (n + 2) :=
  if flag then i.succ else i.castSucc

private theorem chart_barycenter (k : Fin 3) (d : ℝ) (a b : Bool → ℝ) (u v : ℝ) :
    (∑ c : Bool × Bool, rowWeight u v c • chart k d (a c.1) (b c.2)) =
      chart k d ((1 - u) * a false + u * a true) ((1 - v) * b false + v * b true) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_bool]
  fin_cases k <;> fin_cases j <;> simp [chart, rowWeight, rowFactor] <;> ring

private theorem exists_grid_location {g : BulkRowGrid n} {q : ℝ} (hg : g.Sound q)
    {a : ℝ} (ha : |a| ≤ 1) :
    ∃ (i : Fin (n + 1)) (w : ℝ), w ∈ Set.Icc 0 1 ∧
      a = (1 - w) * g.point i.castSucc + w * g.point i.succ := by
  have hl : g.point 0 ≤ a := by rw [hg.first]; exact (abs_le.mp ha).1
  have hh : a ≤ g.point (Fin.last (n + 1)) := by rw [hg.last]; exact (abs_le.mp ha).2
  obtain ⟨i, hi₀, hi₁⟩ := exists_adjacent_knots n hl hh
  obtain ⟨w, hw, hw'⟩ := exists_interval_lerp hi₀ hi₁
  exact ⟨i, w, hw, hw'⟩

private theorem weightedRow_chart {q : ℝ} {t : Profile} {g : BulkRowGrid n}
    {p : Fin 4 → ℕ} {γ : Fin 3 → ℕ} {weightDen : ℕ}
    {upper : Fin 3 → Fin (n + 2) → Fin (n + 2) → Fin 4 → ℤ}
    (hq : 1 ≤ q) (hWeight : 0 < (weightDen : ℝ)) (hg : g.Sound q)
    (hBound : ∀ k a b s, |rowEval t s (g.cornerRow k a b)| ^ q ≤
      (upper k a b s : ℝ) / g.valueDen)
    (hCheck : ∀ k a b, bulkCornerOK p γ (upper k a b) (g.cornerLower k a b) = true)
    (k : Fin 3) {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    WeightedRow q t (fun s => (p s : ℝ) / weightDen) (fun j => (γ j : ℝ) / weightDen)
      (chart k 1 a b) := by
  obtain ⟨i, u, hu, hA⟩ := exists_grid_location hg ha
  obtain ⟨j, v, hv, hB⟩ := exists_grid_location hg hb
  let x (c : Bool × Bool) := g.cornerRow k (adjacent i c.1) (adjacent j c.2)
  have hX : (∑ c, rowWeight u v c • x c) = chart k 1 a b := by
    simp only [x, cornerRow_chart hg]
    rw [chart_barycenter k 1 (fun b' => g.point (adjacent i b')) (fun b' => g.point (adjacent j b'))]
    simpa only [adjacent, Bool.false_eq_true, ↓reduceIte] using
      congrArg₂ (chart k (1 : ℝ)) hA.symm hB.symm
  have hValue : 0 < (g.valueDen : ℝ) := by exact_mod_cast hg.valueDen_pos
  rw [← hX]
  refine weightedRow_of_bulkCorners (vertices := Finset.univ) (x := x) (valueDen := g.valueDen)
    (upper := fun c => upper k (adjacent i c.1) (adjacent j c.2))
    (lower := fun c => g.cornerLower k (adjacent i c.1) (adjacent j c.2))
    hq hWeight hValue ?_ (sum_rowWeight u v) ?_ ?_ ?_
  · exact fun c _ => mul_nonneg (rowFactor_nonneg hu c.1) (rowFactor_nonneg hv c.2)
  · exact fun c _ s => hBound k (adjacent i c.1) (adjacent j c.2) s
  · exact fun c _ => hCheck k (adjacent i c.1) (adjacent j c.2)
  · intro s
    rw [hX]
    have hL := congrFun (chart_barycenter k 1
      (fun b' => g.lower (adjacent i b')) (fun b' => g.lower (adjacent j b')) u v) s
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hL
    simp only [cornerLower_chart hg]
    rw [hL]
    have ha' := hg.lower_lerp i hu
    have hb' := hg.lower_lerp j hv
    rw [← hA] at ha'
    rw [← hB] at hb'
    fin_cases k <;> fin_cases s <;> simp [chart, adjacent, ha', hb']

private theorem exists_chart (k : Fin 3) {x : Row} (hk : x k = 1) (hx : ∀ j, |x j| ≤ 1) :
    ∃ a b, x = chart k 1 a b ∧ |a| ≤ 1 ∧ |b| ≤ 1 := by
  fin_cases k
  · refine ⟨x 1, x 2, ?_, hx 1, hx 2⟩
    funext j; fin_cases j <;> simp [chart]
    exact hk
  · refine ⟨x 0, x 2, ?_, hx 0, hx 2⟩
    funext j; fin_cases j <;> simp [chart]
    exact hk
  · refine ⟨x 0, x 1, ?_, hx 0, hx 1⟩
    funext j; fin_cases j <;> simp [chart]
    exact hk

/-- For a fixed profile, integer corner checks on all three normalized charts
give the weighted row inequality for every real row. -/
theorem weightedRows_of_corners {q : ℝ} {t : Profile} {g : BulkRowGrid n}
    {p : Fin 4 → ℕ} {γ : Fin 3 → ℕ} {weightDen : ℕ}
    {upper : Fin 3 → Fin (n + 2) → Fin (n + 2) → Fin 4 → ℤ}
    (hq : 1 ≤ q) (hWeight : 0 < (weightDen : ℝ)) (hg : g.Sound q)
    (hBound : ∀ k a b s, |rowEval t s (g.cornerRow k a b)| ^ q ≤
      (upper k a b s : ℝ) / g.valueDen)
    (hCheck : ∀ k a b, bulkCornerOK p γ (upper k a b) (g.cornerLower k a b) = true) :
    ∀ x, WeightedRow q t (fun s => (p s : ℝ) / weightDen) (fun j => (γ j : ℝ) / weightDen) x := by
  apply weightedRow_of_normalized_charts (zero_lt_one.trans_le hq)
  intro k x hk hx
  obtain ⟨a, b, hForm, ha, hb⟩ := exists_chart k hk hx
  rw [hForm]
  exact weightedRow_chart hq hWeight hg hBound hCheck k ha hb

end BulkRowGrid

/-- Tangent endpoint bounds suffice on any signed interval that lies on one
side of zero, including intervals incident to zero. -/
theorem signed_tangent_segment_lower {q m a b νa νb w : ℝ}
    (hq : 1 ≤ q) (hm : 0 < m) (hw : w ∈ Set.Icc 0 1)
    (hSign : (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0))
    (hA : νa ≤ m ^ q * (1 + q * (|a| / m - 1)))
    (hB : νb ≤ m ^ q * (1 + q * (|b| / m - 1))) :
    (1 - w) * νa + w * νb ≤ |(1 - w) * a + w * b| ^ q := by
  have hw' := sub_nonneg.mpr hw.2
  have hAbs : |(1 - w) * a + w * b| = (1 - w) * |a| + w * |b| := by
    rcases hSign with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [abs_of_nonneg ha, abs_of_nonneg hb,
        abs_of_nonneg (add_nonneg (mul_nonneg hw' ha) (mul_nonneg hw.1 hb))]
    · rw [abs_of_nonpos ha, abs_of_nonpos hb,
        abs_of_nonpos (add_nonpos (mul_nonpos_of_nonneg_of_nonpos hw' ha)
          (mul_nonpos_of_nonneg_of_nonpos hw.1 hb))]
      ring
  let tangent (x : ℝ) := m ^ q * (1 + q * (x / m - 1))
  have hy : 0 ≤ (1 - w) * |a| + w * |b| :=
    add_nonneg (mul_nonneg hw' (abs_nonneg _)) (mul_nonneg hw.1 (abs_nonneg _))
  rw [hAbs]
  calc
    _ ≤ (1 - w) * tangent |a| + w * tangent |b| :=
      add_le_add (mul_le_mul_of_nonneg_left hA hw') (mul_le_mul_of_nonneg_left hB hw.1)
    _ = tangent ((1 - w) * |a| + w * |b|) := by simp only [tangent, div_eq_mul_inv]; ring
    _ ≤ _ := tangentRatio_le_rpow hq hm hy

end

end HlawkaSchatten.BelowExponent
