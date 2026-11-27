/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.Real
import HlawkaSchatten.BelowExponent.BulkGeometry

/-! Real interpolation on the sign-constant row rectangles used by tangent certificates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Tangent

open Set

noncomputable section

def chartRow (j : Fin 3) (a b : ℝ) : Row :=
  ![![1, a, b], ![a, 1, b], ![a, b, 1]] j

def chartA (j : Fin 3) : Fin 3 := ![1, 0, 0] j

def chartB (j : Fin 3) : Fin 3 := ![2, 2, 1] j

def chartCoord (C : TC.Ctx) (a : ℝ) : ℝ := a / C.Da - 1

/-- The lower bound represented by a TC row tangent, evaluated at a signed coordinate. -/
def rowTangent (C : TC.Ctx) (code : ℕ) (x : ℝ) : ℝ :=
  (-(↑(TC.acoef C code).1 : ℝ) + ↑(TC.acoef C code).2 * |x|) / 2 ^ C.K

def cornerOutput (q : ℝ) (t π : Profile) (x : Row) : ℝ :=
  ∑ s, π s * |rowEval t s x| ^ q

def cornerInput (γ : Row) (j : Fin 3) (L M : ℝ → ℝ) (a b : ℝ) : ℝ :=
  γ j + γ (chartA j) * L a + γ (chartB j) * M b

private theorem chartRow_lerpA (j : Fin 3) (a₀ a₁ b u : ℝ) :
    chartRow j ((1 - u) * a₀ + u * a₁) b =
      (1 - u) • chartRow j a₀ b + u • chartRow j a₁ b := by
  funext i
  fin_cases j <;> fin_cases i <;> simp [chartRow, smul_eq_mul] <;> ring

private theorem chartRow_lerpB (j : Fin 3) (a b₀ b₁ u : ℝ) :
    chartRow j a ((1 - u) * b₀ + u * b₁) =
      (1 - u) • chartRow j a b₀ + u • chartRow j a b₁ := by
  funext i
  fin_cases j <;> fin_cases i <;> simp [chartRow, smul_eq_mul] <;> ring

private theorem cornerOutput_convex {q : ℝ} (hq : 1 ≤ q) {t π : Profile}
    (hπ : ∀ s, 0 ≤ π s) : ConvexOn ℝ (univ : Set Row) (cornerOutput q t π) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [cornerOutput, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  calc
    _ ≤ π s * (a * |rowEval t s x| ^ q + b * |rowEval t s y| ^ q) :=
      mul_le_mul_of_nonneg_left ((convexOn_abs_rowEval_row_rpow hq t s).2
        (mem_univ x) (mem_univ y) ha hb hab) (hπ s)
    _ = _ := by ring

private theorem rect_le_of_corners {q : ℝ} (hq : 1 ≤ q) {t π : Profile}
    (hπ : ∀ s, 0 ≤ π s) (j : Fin 3) {A₀ A₁ B₀ B₁ a b c d e : ℝ}
    (ha : a ∈ Icc A₀ A₁) (hb : b ∈ Icc B₀ B₁)
    (hcorner : ∀ A ∈ ({A₀, A₁} : Set ℝ), ∀ B ∈ ({B₀, B₁} : Set ℝ),
      cornerOutput q t π (chartRow j A B) ≤ c + d * A + e * B) :
    cornerOutput q t π (chartRow j a b) ≤ c + d * a + e * b := by
  have hc := cornerOutput_convex hq (t := t) hπ
  obtain ⟨u, hu, hA⟩ := exists_interval_lerp ha.1 ha.2
  obtain ⟨v, hv, hB⟩ := exists_interval_lerp hb.1 hb.2
  have hline (A : ℝ) (hmm : A ∈ ({A₀, A₁} : Set ℝ)) :
      cornerOutput q t π (chartRow j A b) ≤ c + d * A + e * b := by
    calc
      _ ≤ (1 - v) * cornerOutput q t π (chartRow j A B₀) +
          v * cornerOutput q t π (chartRow j A B₁) := by
        rw [hB, chartRow_lerpB]
        exact hc.2 (mem_univ _) (mem_univ _) (sub_nonneg.mpr hv.2) hv.1 (sub_add_cancel 1 v)
      _ ≤ (1 - v) * (c + d * A + e * B₀) + v * (c + d * A + e * B₁) :=
        add_le_add (mul_le_mul_of_nonneg_left (hcorner A hmm B₀ (by simp)) (sub_nonneg.mpr hv.2))
          (mul_le_mul_of_nonneg_left (hcorner A hmm B₁ (by simp)) hv.1)
      _ = _ := by rw [hB]; ring
  calc
    _ ≤ (1 - u) * cornerOutput q t π (chartRow j A₀ b) +
        u * cornerOutput q t π (chartRow j A₁ b) := by
      rw [hA, chartRow_lerpA]
      exact hc.2 (mem_univ _) (mem_univ _) (sub_nonneg.mpr hu.2) hu.1 (sub_add_cancel 1 u)
    _ ≤ (1 - u) * (c + d * A₀ + e * b) + u * (c + d * A₁ + e * b) :=
      add_le_add (mul_le_mul_of_nonneg_left (hline A₀ (by simp)) (sub_nonneg.mpr hu.2))
        (mul_le_mul_of_nonneg_left (hline A₁ (by simp)) hu.1)
    _ = _ := by rw [hA]; ring

private theorem abs_eq_mul_on_Icc {a b : ℝ} (h : 0 ≤ a ∨ b ≤ 0) :
    ∃ s : ℝ, ∀ x ∈ Icc a b, |x| = s * x := by
  rcases h with h | h
  · exact ⟨1, fun _ hx => by rw [one_mul, abs_of_nonneg (h.trans hx.1)]⟩
  · exact ⟨-1, fun _ hx => by rw [neg_one_mul, abs_of_nonpos (hx.2.trans h)]⟩

private theorem endpoints_mem_Icc {a b x : ℝ} (h : a ≤ b) (hx : x ∈ ({a, b} : Set ℝ)) :
    x ∈ Icc a b := by
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact ⟨le_rfl, h⟩
  · rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨h, le_rfl⟩

/-- Four compensated comparisons prove the row estimate on a closed signed rectangle. -/
theorem weightedRow_of_signed_rectangle {q : ℝ} (hq : 1 ≤ q) {t π : Profile} {γ : Row}
    (hπ : ∀ s, 0 ≤ π s) (hγ : ∀ i, 0 ≤ γ i) (j : Fin 3)
    {A₀ A₁ B₀ B₁ a b aC aD bC bD : ℝ}
    (ha : a ∈ Icc A₀ A₁) (hb : b ∈ Icc B₀ B₁)
    (hsA : 0 ≤ A₀ ∨ A₁ ≤ 0) (hsB : 0 ≤ B₀ ∨ B₁ ≤ 0)
    (hA : aC + aD * |a| ≤ |a| ^ q) (hB : bC + bD * |b| ≤ |b| ^ q)
    (hcorner : ∀ A ∈ ({A₀, A₁} : Set ℝ), ∀ B ∈ ({B₀, B₁} : Set ℝ),
      cornerOutput q t π (chartRow j A B) ≤
        cornerInput γ j (fun x => aC + aD * |x|) (fun x => bC + bD * |x|) A B) :
    WeightedRow q t π γ (chartRow j a b) := by
  obtain ⟨σ, hσ⟩ := abs_eq_mul_on_Icc hsA
  obtain ⟨τ, hτ⟩ := abs_eq_mul_on_Icc hsB
  let L (x : ℝ) := aC + aD * |x|
  let M (x : ℝ) := bC + bD * |x|
  have heq {A B : ℝ} (hA' : A ∈ Icc A₀ A₁) (hB' : B ∈ Icc B₀ B₁) :
      cornerInput γ j L M A B = γ j + γ (chartA j) * aC + γ (chartB j) * bC +
        (γ (chartA j) * aD * σ) * A + (γ (chartB j) * bD * τ) * B := by
    simp only [cornerInput, L, M, hσ A hA', hτ B hB']
    ring
  have hle : cornerOutput q t π (chartRow j a b) ≤ cornerInput γ j L M a b := by
    rw [heq ha hb]
    apply rect_le_of_corners hq hπ j ha hb
    intro A hAm B hBm
    rw [← heq (endpoints_mem_Icc (ha.1.trans ha.2) hAm) (endpoints_mem_Icc (hb.1.trans hb.2) hBm)]
    exact hcorner A hAm B hBm
  unfold WeightedRow
  change cornerOutput q t π (chartRow j a b) ≤ _
  refine hle.trans ?_
  have hγa := mul_le_mul_of_nonneg_left hA (hγ (chartA j))
  have hγb := mul_le_mul_of_nonneg_left hB (hγ (chartB j))
  fin_cases j <;> simp [cornerInput, L, M, chartRow, chartA, chartB, Fin.sum_univ_three]
    at hγa hγb ⊢ <;> linarith only [hγa, hγb]

/-- The projections used by the checker enumerate exactly the three normalized faces. -/
theorem weightedRow_of_chart_squares {q : ℝ} {t π : Profile} {γ : Row} (hq : 0 < q)
    (hchart : ∀ (j : Fin 3) a b, |a| ≤ 1 → |b| ≤ 1 →
      WeightedRow q t π γ (chartRow j a b)) (x : Row) : WeightedRow q t π γ x := by
  apply weightedRow_of_normalized_charts hq _ x
  intro j y hj hy
  have hrow : chartRow j (y (chartA j)) (y (chartB j)) = y := by
    funext i
    fin_cases j <;> fin_cases i <;> simp_all [chartRow, chartA, chartB]
  rw [← hrow]
  exact hchart j _ _ (hy (chartA j)) (hy (chartB j))

/-- The semantic content needed from arithmetic at one checked corner. -/
def CornerSound (q : ℝ) (C : TC.Ctx) (F : TC.Face) (j : Fin 3)
    (t π : Profile) (γ : Row) : Prop :=
  ∀ (ca cb A B : ℕ),
    let add := (F.gk * (TC.acoef C ca).1 + F.gl * (TC.acoef C cb).1) * C.Da * F.F
    TC.cornerOK C F add (TC.acoef C ca).2 (TC.acoef C cb).2 A B (TC.lmaxAt C F A B) = true →
      cornerOutput q t π (chartRow j (chartCoord C A) (chartCoord C B)) ≤
        cornerInput γ j (rowTangent C ca) (rowTangent C cb) (chartCoord C A) (chartCoord C B)

private theorem chartCoord_mono {C : TC.Ctx} : Monotone (chartCoord C) := by
  intro x y h
  exact sub_le_sub_right (div_le_div_of_nonneg_right h (Nat.cast_nonneg _)) _

private theorem chartCoord_Da {C : TC.Ctx} (hD : 0 < C.Da) : chartCoord C C.Da = 0 := by
  have hD' : (C.Da : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  simp [chartCoord, hD']

private theorem chartCoord_signed {C : TC.Ctx} (hD : 0 < C.Da) {l r : ℕ}
    (h : C.Da ≤ l ∨ r ≤ C.Da) : 0 ≤ chartCoord C l ∨ chartCoord C r ≤ 0 := by
  rcases h with h | h
  · left
    rw [← chartCoord_Da hD]
    exact chartCoord_mono (by exact_mod_cast h)
  · right
    rw [← chartCoord_Da hD]
    exact chartCoord_mono (by exact_mod_cast h)

theorem weightedRow_of_numeric_leaf {q : ℝ} (hq : 1 ≤ q) {C : TC.Ctx} (hD : 0 < C.Da)
    {F : TC.Face} {j : Fin 3} {t π : Profile} {γ : Row}
    (hπ : ∀ s, 0 ≤ π s) (hγ : ∀ i, 0 ≤ γ i)
    (htan : ∀ code x, rowTangent C code x ≤ |x| ^ q) (hcorner : CornerSound q C F j t π γ)
    {A₀ A₁ B₀ B₁ ca cb : ℕ} {a b : ℝ}
    (h : TC.leafOK C F A₀ A₁ B₀ B₁ ca cb (TC.lmaxAt C F A₀ B₀) (TC.lmaxAt C F A₀ B₁)
      (TC.lmaxAt C F A₁ B₀) (TC.lmaxAt C F A₁ B₁) = true)
    (ha : a ∈ Icc (A₀ : ℝ) A₁) (hb : b ∈ Icc (B₀ : ℝ) B₁) :
    WeightedRow q t π γ (chartRow j (chartCoord C a) (chartCoord C b)) := by
  obtain ⟨hsA, hsB, h00, h01, h10, h11⟩ := TC.leafOK_spec _ _ _ _ _ _ _ _ _ _ _ _ h
  have hm := chartCoord_mono (C := C)
  have ha' : chartCoord C a ∈ Icc (chartCoord C A₀) (chartCoord C A₁) := ⟨hm ha.1, hm ha.2⟩
  have hb' : chartCoord C b ∈ Icc (chartCoord C B₀) (chartCoord C B₁) := ⟨hm hb.1, hm hb.2⟩
  have htanEq (code : ℕ) (x : ℝ) : rowTangent C code x =
      -(↑(TC.acoef C code).1 : ℝ) / 2 ^ C.K + (↑(TC.acoef C code).2 : ℝ) / 2 ^ C.K * |x| := by
    unfold rowTangent
    rw [add_div, mul_div_right_comm]
  refine weightedRow_of_signed_rectangle hq hπ hγ j ha' hb' (chartCoord_signed hD hsA)
    (chartCoord_signed hD hsB) (htanEq ca _ ▸ htan ca _) (htanEq cb _ ▸ htan cb _) ?_
  intro A hA B hB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · simpa only [← htanEq] using hcorner ca cb A₀ B₀ h00
  · simpa only [← htanEq] using hcorner ca cb A₀ B₁ h01
  · simpa only [← htanEq] using hcorner ca cb A₁ B₀ h10
  · simpa only [← htanEq] using hcorner ca cb A₁ B₁ h11

theorem weightedRow_of_face_cover {q : ℝ} (hq : 1 ≤ q) {C : TC.Ctx} (hD : 0 < C.Da)
    {F : TC.Face} {j : Fin 3} {t π : Profile} {γ : Row}
    (hπ : ∀ s, 0 ≤ π s) (hγ : ∀ i, 0 ≤ γ i)
    (htan : ∀ code x, rowTangent C code x ≤ |x| ^ q) (hcorner : CornerSound q C F j t π γ)
    {A₀ A₁ B₀ B₁ : ℕ} (h : TC.BoxCover (TC.LeafP C F) A₀ A₁ B₀ B₁)
    {a b : ℝ} (ha : a ∈ Icc (A₀ : ℝ) A₁) (hb : b ∈ Icc (B₀ : ℝ) B₁) :
    WeightedRow q t π γ (chartRow j (chartCoord C a) (chartCoord C b)) := by
  obtain ⟨_, _, _, _, ⟨ca, cb, h⟩, ha, hb⟩ := exists_leaf_at h ha hb
  exact weightedRow_of_numeric_leaf hq hD hπ hγ htan hcorner h ha hb

theorem signed_coord_to_offset {C : TC.Ctx} (hD : 0 < C.Da) {a : ℝ} (ha : |a| ≤ 1) :
    ∃ A ∈ Icc (0 : ℝ) (2 * C.Da), chartCoord C A = a := by
  have hD' : (0 : ℝ) < C.Da := by exact_mod_cast hD
  obtain ⟨hlo, hhi⟩ := abs_le.mp ha
  refine ⟨(1 + a) * C.Da, ⟨mul_nonneg (by linarith only [hlo]) hD'.le, ?_⟩, ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith only [hhi]) hD'.le
  · unfold chartCoord
    rw [mul_div_cancel_right₀ _ hD'.ne']
    ring

end

end HlawkaSchatten.BelowExponent.Tangent
