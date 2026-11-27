/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetConeBox
public import HlawkaSchatten.BelowExponent.Tangent.Rectangle
import Mathlib.Data.List.GetD

/-! Use the same signed rectangle proof for the F and G2 prism certificates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

open Set

noncomputable section

def vertexAt (P : Prism) (v : Fin 3) (cap : Bool) : TC.V4 :=
  P.vertices.getD (v.val + if cap then 3 else 0) ⟨0, 0, 0, 0⟩

def realVertex (P : Prism) (v : Fin 3) (cap : Bool) : Profile :=
  Tangent.vertex P.profileDen (vertexAt P v cap)

def realPi (P : Prism) (s : Fin 4) : ℝ :=
  (P.pi.getD s.val 0 : ℝ) / weightDen

def realInput (P : Prism) (v : TC.V4) (j : Fin 3) : ℝ :=
  (inputNumerator P v j.val : ℝ) / ((weightDen : ℝ) * P.profileDen)

def realGamma (P : Prism) (v : Fin 3) (cap : Bool) : Row :=
  realInput P (vertexAt P v cap)

def vertexFace (P : Prism) (v : TC.V4) (j : Fin 3) : TC.Face :=
  TC.mkFace ctx [v] P.profileDen (P.pi.map (· * P.profileDen))
    ((vertexInputs P v).map Int.toNat) j.val (Tangent.chartA j).val (Tangent.chartB j).val

theorem vertexFace_mem (P : Prism) {v : TC.V4} (hv : v ∈ P.vertices) (j : Fin 3) :
    (v.v3 == 0, vertexFace P v j) ∈ chartFaces P j.val (Tangent.chartA j).val (Tangent.chartB j).val :=
  List.mem_map.mpr ⟨v, hv, rfl⟩

theorem realPi_nonneg (P : Prism) (s : Fin 4) : 0 ≤ realPi P s :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem inputNumerator_nonneg {P : Prism} (h : dataOK P = true) {v : TC.V4} (hv : v ∈ P.vertices)
    (j : Fin 3) : 0 ≤ inputNumerator P v j.val := by
  have hchecks := (Bool.and_eq_true_iff.mp h).2
  have hrow := List.all_eq_true.mp hchecks v hv
  have hnums := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hrow).2).1
  have hj : inputNumerator P v j.val ∈ vertexInputs P v := by
    fin_cases j <;> simp [vertexInputs]
  exact of_decide_eq_true (List.all_eq_true.mp hnums _ hj)

theorem realInput_nonneg {P : Prism} (h : dataOK P = true) {v : TC.V4} (hv : v ∈ P.vertices)
    (j : Fin 3) : 0 ≤ realInput P v j := by
  apply div_nonneg _ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact_mod_cast inputNumerator_nonneg h hv j

theorem profileDen_pos {P : Prism} (h : dataOK P = true) : 0 < P.profileDen := by
  simp only [dataOK, Bool.and_eq_true, TC.blt_true] at h
  exact h.1.1.1.1.2

theorem pi_length {P : Prism} (h : dataOK P = true) : P.pi.length = 4 := by
  simp only [dataOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.2

theorem realPi_faceWeights {P : Prism} (h : dataOK P = true) (s : Fin 4) :
    realPi P s = ((P.pi.map (· * P.profileDen)).getD s.val 0 : ℝ) /
      ((weightDen * P.profileDen : ℕ) : ℝ) := by
  have hd : (P.profileDen : ℝ) ≠ 0 := by exact_mod_cast (profileDen_pos h).ne'
  have heq : ((P.pi.map (· * P.profileDen)).getD s.val 0) = P.pi.getD s.val 0 * P.profileDen := by
    simpa only [Nat.zero_mul] using List.getD_map P.pi 0 (· * P.profileDen) (n := s.val)
  rw [heq]
  push_cast
  unfold realPi
  rw [mul_div_mul_right _ _ hd]

theorem realInput_faceWeights {P : Prism} (h : dataOK P = true) {v : TC.V4} (hv : v ∈ P.vertices)
    (j : Fin 3) : realInput P v j = (((vertexInputs P v).map Int.toNat).getD j.val 0 : ℝ) /
      ((weightDen * P.profileDen : ℕ) : ℝ) := by
  have hpos := inputNumerator_nonneg h hv j
  have hcast : ((inputNumerator P v j.val).toNat : ℝ) = (inputNumerator P v j.val : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hpos
  have hvalue : ((vertexInputs P v).map Int.toNat).getD j.val 0 = (inputNumerator P v j.val).toNat := by
    fin_cases j <;> rfl
  rw [hvalue, hcast]
  push_cast
  rfl

theorem vertexAt_mem {P : Prism} (h : dataOK P = true) (v : Fin 3) (cap : Bool) :
    vertexAt P v cap ∈ P.vertices := by
  have hn : P.vertices.length = 6 := by
    simp only [dataOK, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1.1.1.1.1.1
  have hi : v.val + (if cap then 3 else 0) < P.vertices.length := by
    cases cap <;> simp_all <;> omega
  rw [vertexAt, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _

/-- A passing prism covers every physical row at a represented vertex. -/
theorem vertexRows_of_numeric {P : Prism} (h : dataOK P = true) {v : TC.V4} (hv : v ∈ P.vertices)
    (trees : Fin 3 → RowTree)
    (hcharts : ∀ j : Fin 3, checkChart P j.val (Tangent.chartA j).val (Tangent.chartB j).val (trees j) = true)
    (htan : ∀ code x, Tangent.rowTangent ctx code x ≤ |x| ^ criticalQ)
    (hcorners : ∀ j, Tangent.CornerSound criticalQ ctx (vertexFace P v j) j
      (Tangent.vertex P.profileDen v) (realPi P) (realInput P v))
    (hcone : v.v3 = 0 → ∀ x, FacetRatioCone ((P.radiusNum : ℝ) / P.radiusDen) x →
      WeightedRow criticalQ (Tangent.vertex P.profileDen v) (realPi P) (realInput P v) x) :
    ∀ x, WeightedRow criticalQ (Tangent.vertex P.profileDen v) (realPi P) (realInput P v) x := by
  have hq : 1 ≤ criticalQ := (by norm_num : (1 : ℝ) ≤ 1054 / 665).trans criticalQ_bracket.1.le
  have hD : 0 < ctx.Da := by decide
  have hr : 0 < P.radiusDen := by
    simp only [dataOK, Bool.and_eq_true, TC.blt_true] at h
    have hrad := h.1.1.2
    omega
  apply Tangent.weightedRow_of_chart_squares (zero_lt_one.trans_le hq)
  intro j a b ha hb
  obtain ⟨A, hA, ha'⟩ := Tangent.signed_coord_to_offset hD ha
  obtain ⟨B, hB, hb'⟩ := Tangent.signed_coord_to_offset hD hb
  rw [← ha', ← hb']
  have hA' : A ∈ Icc ((0 : ℕ) : ℝ) (((2 * ctx.Da : ℕ)) : ℝ) := by push_cast; exact hA
  have hB' : B ∈ Icc ((0 : ℕ) : ℝ) (((2 * ctx.Da : ℕ)) : ℝ) := by push_cast; exact hB
  obtain ⟨_, _, _, _, hbox, hAlocal, hBlocal⟩ :=
    Tangent.exists_leaf_at (checkChart_cover P _ _ _ (hcharts j)) hA' hB'
  rcases hbox.vertex (vertexFace_mem P hv j) with ⟨hbase, hc⟩ | ⟨ca, cb, hgate⟩
  · have hv0 : v.v3 = 0 := beq_iff_eq.mp hbase
    exact hcone hv0 _ (isConeBox_sound P hr hc hA.1 hB.1 hB.2 hAlocal.2 hBlocal.1 hBlocal.2)
  · exact Tangent.weightedRow_of_numeric_leaf hq hD (realPi_nonneg P) (realInput_nonneg h hv)
      htan (hcorners j) hgate hAlocal hBlocal

def PrismCornerSound (P : Prism) : Prop :=
  ∀ (v : Fin 3) (cap : Bool) (j : Fin 3),
    Tangent.CornerSound criticalQ ctx (vertexFace P (vertexAt P v cap) j) j
      (realVertex P v cap) (realPi P) (realGamma P v cap)

theorem prismRows_of_numeric {P : Prism} (h : dataOK P = true)
    (trees : Fin 3 → RowTree)
    (hcharts : ∀ j : Fin 3, checkChart P j.val (Tangent.chartA j).val (Tangent.chartB j).val (trees j) = true)
    (htan : ∀ code x, Tangent.rowTangent ctx code x ≤ |x| ^ criticalQ)
    (hcorners : PrismCornerSound P)
    (hcone : ∀ v cap, (vertexAt P v cap).v3 = 0 → ∀ x,
      FacetRatioCone ((P.radiusNum : ℝ) / P.radiusDen) x →
      WeightedRow criticalQ (realVertex P v cap) (realPi P) (realGamma P v cap) x) :
    ∀ v cap x, WeightedRow criticalQ (realVertex P v cap) (realPi P) (realGamma P v cap) x :=
  fun v cap => vertexRows_of_numeric h (vertexAt_mem h v cap) trees hcharts htan
    (hcorners v cap) (hcone v cap)

end

end HlawkaSchatten.BelowExponent.FacetNumeric
