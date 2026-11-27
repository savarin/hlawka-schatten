/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.NearChecker
public import HlawkaSchatten.BelowExponent.FacetTangentPrism
import all HlawkaSchatten.BelowExponent.FacetTangentPrism
import Batteries.Tactic.OpenPrivate

/-! The two refined charts use exact Taylor leaves alongside the ordinary tangent leaves. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

open Set
open private prismWeight_base from HlawkaSchatten.BelowExponent.FacetTangentPrism

def mixedLeaf (P : Prism) (j : Fin 3) (a₁ a₂ b₁ b₂ : ℕ) : Prop :=
  nearChartBox P j a₁ a₂ b₁ b₂ = true ∨
    PassingBox P j.val (chartFaces P j.val (Tangent.chartA j).val (Tangent.chartB j).val) a₁ a₂ b₁ b₂

/-- The reserved code selects a Taylor leaf. Ordinary numeric leaves have their original semantics. -/
def checkMixed (P : Prism) (j : Fin 3) (faces : List (Bool × TC.Face)) :
    RowTree → ℕ → ℕ → ℕ → ℕ → Bool
  | .splitA left right, a₁, a₂, b₁, b₂ =>
    let m := (a₁+a₂)/2
    Nat.ble a₁ m && Nat.ble m a₂ &&
      checkMixed P j faces left a₁ m b₁ b₂ && checkMixed P j faces right m a₂ b₁ b₂
  | .splitB left right, a₁, a₂, b₁, b₂ =>
    let m := (b₁+b₂)/2
    Nat.ble b₁ m && Nat.ble m b₂ &&
      checkMixed P j faces left a₁ a₂ b₁ m && checkMixed P j faces right a₁ a₂ m b₂
  | .box ca cb, a₁, a₂, b₁, b₂ =>
    if ca = 10000 then nearChartBox P j a₁ a₂ b₁ b₂
    else checkTree P j.val faces (.box ca cb) a₁ a₂ b₁ b₂

def checkMixedChart (P : Prism) (j : Fin 3) (tree : RowTree) : Bool :=
  checkMixed P j (chartFaces P j.val (Tangent.chartA j).val (Tangent.chartB j).val) tree
    0 (2*ctx.Da) 0 (2*ctx.Da)

private theorem mixedCover (P : Prism) (j : Fin 3) {tree : RowTree} {a₁ a₂ b₁ b₂ : ℕ}
    (h : checkMixed P j (chartFaces P j.val (Tangent.chartA j).val (Tangent.chartB j).val)
      tree a₁ a₂ b₁ b₂ = true) : TC.BoxCover (mixedLeaf P j) a₁ a₂ b₁ b₂ := by
  induction tree generalizing a₁ a₂ b₁ b₂ with
  | box ca cb =>
    unfold checkMixed at h
    split at h
    · exact .leaf (Or.inl h)
    · exact .leaf (Or.inr ⟨ca, cb, h⟩)
  | splitA left right ihₗ ihᵣ =>
    simp only [checkMixed, Bool.and_eq_true, TC.ble_true, and_assoc] at h
    exact .splitA _ h.1 h.2.1 (ihₗ h.2.2.1) (ihᵣ h.2.2.2)
  | splitB left right ihₗ ihᵣ =>
    simp only [checkMixed, Bool.and_eq_true, TC.ble_true, and_assoc] at h
    exact .splitB _ h.1 h.2.1 (ihₗ h.2.2.1) (ihᵣ h.2.2.2)

theorem prismRows_of_mixed {P : Prism} (h : dataOK P = true)
    (trees : Fin 3 → RowTree) (hcharts : ∀ j, checkMixedChart P j (trees j) = true)
    (hcone : ∀ v cap, (vertexAt P v cap).v3 = 0 → ∀ x,
      FacetRatioCone ((P.radiusNum : ℝ) / P.radiusDen) x →
      WeightedRow criticalQ (realVertex P v cap) (realPi P) (realGamma P v cap) x) :
    ∀ v cap x, WeightedRow criticalQ (realVertex P v cap) (realPi P) (realGamma P v cap) x := by
  intro i cap
  let v := vertexAt P i cap
  change ∀ x, WeightedRow criticalQ (Tangent.vertex P.profileDen v) (realPi P) (realInput P v) x
  have hv := vertexAt_mem h i cap
  have hcorners := prismCornerSound_of_numeric h i cap
  have hq : 1 ≤ criticalQ := (by norm_num : (1:ℝ) ≤ 1054/665).trans criticalQ_bracket.1.le
  have hD : 0 < ctx.Da := by decide
  have hr : 0 < P.radiusDen := by
    have hh := h
    simp only [dataOK, Bool.and_eq_true, TC.blt_true] at hh
    have hrad := hh.1.1.2
    omega
  apply Tangent.weightedRow_of_chart_squares (zero_lt_one.trans_le hq)
  intro j a b ha hb
  obtain ⟨A, hA, ha'⟩ := Tangent.signed_coord_to_offset hD ha
  obtain ⟨B, hB, hb'⟩ := Tangent.signed_coord_to_offset hD hb
  rw [← ha', ← hb']
  have hA' : A ∈ Icc ((0:ℕ):ℝ) ((2*ctx.Da:ℕ):ℝ) := by push_cast; exact hA
  have hB' : B ∈ Icc ((0:ℕ):ℝ) ((2*ctx.Da:ℕ):ℝ) := by push_cast; exact hB
  obtain ⟨al, ar, bl, br, hleaf, hal, hbl⟩ :=
    Tangent.exists_leaf_at (mixedCover P j (hcharts j)) hA' hB'
  have hc (hv₀ : v.v3 = 0) (hg : isConeBox P j.val ar bl br = true) :
      WeightedRow criticalQ (Tangent.vertex P.profileDen v) (realPi P) (realInput P v)
        (Tangent.chartRow j (Tangent.chartCoord ctx A) (Tangent.chartCoord ctx B)) :=
    hcone i cap hv₀ _ (isConeBox_sound P hr hg hA.1 hB.1 hB.2 hal.2 hbl.1 hbl.2)
  rcases hleaf with hl | hl
  · rcases nearChartBox_sound h hv hl hal hbl with ⟨hv₀, hcone'⟩ | hrow
    · exact hc hv₀ hcone'
    · exact hrow
  · rcases hl.vertex (vertexFace_mem P hv j) with ⟨hv₀, hcone'⟩ | ⟨ca, cb, hpass⟩
    · exact hc (beq_iff_eq.mp hv₀) hcone'
    · exact Tangent.weightedRow_of_numeric_leaf hq hD (realPi_nonneg P) (realInput_nonneg h hv)
        facetRowTangent_le (hcorners j) hpass hal hbl

theorem rowAt_facetPrism_of_mixed {P : Prism} {b : Fin 3 → Row} {π : Profile} {slope α : Row}
    {d : ℝ} (hα : ∀ i, 0 ≤ α i) (hαsum : ∑ i, α i = 1) (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1/400)
    (hπ : IsSimplex π)
    (hvertex : ∀ i cap, realVertex P i cap = facetCap (b i) (if cap then 1/400 else 0))
    (hweight : realPi P = π)
    (hinput : ∀ i cap, realGamma P i cap =
      prismWeight π slope (facetCap (b i) (if cap then 1/400 else 0)))
    (hbudget : ∀ i (cap : Bool),
      (∀ j, 0 ≤ prismWeight π slope (facetCap (b i) (if cap then 1/400 else 0)) j) ∧
      ∑ j, prismWeight π slope (facetCap (b i) (if cap then 1/400 else 0)) j ≤ 1)
    (hcap : ∀ i, (vertexAt P i true).v3 ≠ 0)
    (hcone : ∀ i x, FacetRatioCone ((P.radiusNum : ℝ) / P.radiusDen) x →
      WeightedRow criticalQ (facetBase (b i)) π (facetWeight π (b i)) x)
    (h : dataOK P = true) (trees : Fin 3 → RowTree)
    (hcharts : ∀ j, checkMixedChart P j (trees j) = true) :
    RowAt criticalQ (facetCap (fun j => ∑ i, α i * b i j) d) := by
  apply rowAt_facet_prism facetCritical_one_lt.le (by norm_num : 0 < (1/400 : ℝ)) hd₀ hd₁ hα hαsum hπ
    (fun i cap => (hbudget i cap).1) (fun i cap => (hbudget i cap).2)
  intro i cap x
  have hrow := prismRows_of_mixed h trees hcharts ?_ i cap x
  · simpa only [hvertex, hweight, hinput] using hrow
  · intro v cap hz x hx
    cases cap
    · rw [hvertex, hweight, hinput]
      simp only [Bool.false_eq_true, ↓reduceIte, facetCap_at_zero, prismWeight_base]
      exact hcone v x hx
    · exact False.elim (hcap v hz)

end HlawkaSchatten.BelowExponent.FacetNumeric
