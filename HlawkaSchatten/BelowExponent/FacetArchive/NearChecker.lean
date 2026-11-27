/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetArchive.NearPower
public import HlawkaSchatten.BelowExponent.FacetTangentArithmetic
import all HlawkaSchatten.BelowExponent.Tangent.Coefficients
import all HlawkaSchatten.BelowExponent.Tangent.Rectangle
import Batteries.Tactic.OpenPrivate

/-! Exact corner checks for the two prisms needing finer near-equality tangents. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

open Set
open private abs_chartCoord rowEval_mkTm from HlawkaSchatten.BelowExponent.Tangent.Coefficients
open private chartCoord_mono chartCoord_signed from HlawkaSchatten.BelowExponent.Tangent.Rectangle

def nearShiftedMag (a : ℕ) : ℕ :=
  bif Nat.ble ctx.Da a then a - ctx.Da else ctx.Da - a

def nearMagnitude (a : ℕ) : ℚ := (nearShiftedMag a : ℚ) / ctx.Da

def nearAnchor (l r : ℕ) : ℚ := 1 - (nearMagnitude l + nearMagnitude r) / 2

def nearRowMovement (P : Prism) (v : TC.V4) (j : Fin 3) (a b : ℕ) (s : Fin 4) : ℚ :=
  let term := TC.mkTm ctx.Da v j.val (Tangent.chartA j).val (Tangent.chartB j).val s.val 0
  |(TC.gInt term (Nat.ble ctx.Da a) (nearShiftedMag a) (Nat.ble ctx.Da b) (nearShiftedMag b) : ℚ) /
    ((P.profileDen : ℚ) * ctx.Da)| - 1

def nearCorner (P : Prism) (v : TC.V4) (j : Fin 3) (a b : ℕ) (r s : ℚ) : Bool :=
  let output := ∑ i : Fin 4, (P.pi.getD i.val 0 : ℚ) * P.profileDen * nearUpper (nearRowMovement P v j a b i)
  let input := fun i : Fin 3 => (inputNumerator P v i.val : ℚ)
  let tangent := fun (k : ℚ) (z : ℕ) => nearIntercept k - nearSlope k * nearMagnitude z
  ((List.finRange 4).all fun i => decide (-1 < nearRowMovement P v j a b i)) &&
    decide (output ≤ input j + input (Tangent.chartA j) * tangent r a + input (Tangent.chartB j) * tangent s b)

def nearBox (P : Prism) (v : TC.V4) (j : Fin 3) (a₁ a₂ b₁ b₂ : ℕ) : Bool :=
  let r := nearAnchor a₁ a₂
  let s := nearAnchor b₁ b₂
  nearCorner P v j a₁ b₁ r s && nearCorner P v j a₁ b₂ r s &&
    nearCorner P v j a₂ b₁ r s && nearCorner P v j a₂ b₂ r s

def nearAxis (l r : ℕ) : Bool :=
  (Nat.ble ctx.Da l || Nat.ble r ctx.Da) &&
    decide (0 ≤ nearAnchor l r ∧ (15/16 : ℚ) ≤ nearMagnitude l ∧ nearMagnitude l ≤ 1 ∧
      (15/16 : ℚ) ≤ nearMagnitude r ∧ nearMagnitude r ≤ 1)

def nearChartBox (P : Prism) (j : Fin 3) (a₁ a₂ b₁ b₂ : ℕ) : Bool :=
  nearAxis a₁ a₂ && nearAxis b₁ b₂ &&
    P.vertices.all fun v => (v.v3 == 0 && isConeBox P j.val a₂ b₁ b₂) || nearBox P v j a₁ a₂ b₁ b₂

private theorem cast_nearMagnitude (a : ℕ) : (nearMagnitude a : ℝ) = |Tangent.chartCoord ctx a| := by
  unfold nearMagnitude
  push_cast
  exact (abs_chartCoord (C := ctx) (by decide) a).symm

private theorem cast_nearRowMovement {P : Prism} (h : dataOK P = true) (v : TC.V4)
    (j : Fin 3) (a b : ℕ) (s : Fin 4) :
    (nearRowMovement P v j a b s : ℝ) =
      |rowEval (Tangent.vertex P.profileDen v) s (Tangent.chartRow j (Tangent.chartCoord ctx a)
        (Tangent.chartCoord ctx b))| - 1 := by
  unfold nearRowMovement
  push_cast
  have heq := rowEval_mkTm (C := ctx) (profileDen_pos h) (by decide) v j s a b 0
  congr 1
  exact congrArg abs heq

private theorem nearCorner_sound {P : Prism} (h : dataOK P = true) {v : TC.V4}
    {j : Fin 3} {a b : ℕ} {r s : ℚ} (hcorner : nearCorner P v j a b r s = true) :
    Tangent.cornerOutput criticalQ (Tangent.vertex P.profileDen v) (realPi P)
        (Tangent.chartRow j (Tangent.chartCoord ctx a) (Tangent.chartCoord ctx b)) ≤
      Tangent.cornerInput (realInput P v) j (fun x => (nearIntercept r : ℝ) - (nearSlope r : ℝ)*|x|)
        (fun x => (nearIntercept s : ℝ) - (nearSlope s : ℝ)*|x|)
        (Tangent.chartCoord ctx a) (Tangent.chartCoord ctx b) := by
  classical
  let x := Tangent.chartRow j (Tangent.chartCoord ctx a) (Tangent.chartCoord ctx b)
  let t := Tangent.vertex P.profileDen v
  let D := (weightDen : ℝ) * P.profileDen
  have hD : 0 < D := by
    have hD' : (0 : ℝ) < P.profileDen := by exact_mod_cast profileDen_pos h
    exact mul_pos (by norm_num [weightDen]) hD'
  simp only [nearCorner, Bool.and_eq_true] at hcorner
  have hpow (i : Fin 4) : |rowEval t i x|^criticalQ ≤ (nearUpper (nearRowMovement P v j a b i) : ℝ) := by
    have hi : -1 < nearRowMovement P v j a b i :=
      of_decide_eq_true (List.all_eq_true.mp hcorner.1 i (List.mem_finRange _))
    have hh := rpow_le_nearUpper hi
    rw [cast_nearRowMovement h, show 1 + (|rowEval t i x|-1) = |rowEval t i x| by ring] at hh
    exact hh
  have hw (i : Fin 4) : realPi P i * D = (P.pi.getD i.val 0 : ℝ) * P.profileDen := by
    unfold D realPi
    field_simp [show (weightDen : ℝ) ≠ 0 by norm_num [weightDen]]
  have hg (i : Fin 3) : realInput P v i * D = (inputNumerator P v i.val : ℝ) := by
    unfold D realInput
    exact div_mul_cancel₀ _ hD.ne'
  have hn := of_decide_eq_true hcorner.2
  have hr := (Rat.cast_le (K := ℝ)).2 hn
  push_cast at hr
  simp only [cast_nearMagnitude] at hr
  apply (mul_le_mul_iff_left₀ hD).1
  unfold Tangent.cornerOutput Tangent.cornerInput
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ i : Fin 4, (P.pi.getD i.val 0 : ℝ) * P.profileDen * (nearUpper (nearRowMovement P v j a b i) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [mul_right_comm, hw]
      exact mul_le_mul_of_nonneg_left (hpow i) (by positivity)
    _ ≤ _ := by
      rw [add_mul, add_mul, mul_right_comm (realInput P v (Tangent.chartA j)),
        mul_right_comm (realInput P v (Tangent.chartB j)), hg, hg, hg]
      exact hr

private theorem nearAxis_sound {l r : ℕ} (h : nearAxis l r = true) {a : ℝ}
    (ha : a ∈ Icc (l:ℝ) r) :
    (0 ≤ Tangent.chartCoord ctx l ∨ Tangent.chartCoord ctx r ≤ 0) ∧
      0 ≤ nearAnchor l r ∧ 0 < |Tangent.chartCoord ctx a| ∧ |Tangent.chartCoord ctx a| ≤ 1 := by
  simp only [nearAxis, Bool.and_eq_true, Bool.or_eq_true, TC.ble_true] at h
  have hs := chartCoord_signed (C := ctx) (by decide) h.1
  obtain ⟨hr, hll, hlu, hrl, hru⟩ := of_decide_eq_true h.2
  have hl₁ : (15/16 : ℝ) ≤ |Tangent.chartCoord ctx l| := by
    rw [← cast_nearMagnitude]
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hll
  have hl₂ : |Tangent.chartCoord ctx l| ≤ 1 := by rw [← cast_nearMagnitude]; exact_mod_cast hlu
  have hr₁ : (15/16 : ℝ) ≤ |Tangent.chartCoord ctx r| := by
    rw [← cast_nearMagnitude]
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hrl
  have hr₂ : |Tangent.chartCoord ctx r| ≤ 1 := by rw [← cast_nearMagnitude]; exact_mod_cast hru
  have hl := chartCoord_mono (C := ctx) ha.1
  have hu := chartCoord_mono (C := ctx) ha.2
  refine ⟨hs, hr, ?_⟩
  rcases hs with hs | hs
  · rw [abs_of_nonneg hs] at hl₁
    rw [abs_of_nonneg (hs.trans (hl.trans hu))] at hr₂
    rw [abs_of_nonneg (hs.trans hl)]
    exact ⟨by linarith only [hl, hl₁], hu.trans hr₂⟩
  · rw [abs_of_nonpos (hl.trans (hu.trans hs))] at hl₂
    rw [abs_of_nonpos hs] at hr₁
    rw [abs_of_nonpos (hu.trans hs)]
    exact ⟨by linarith only [hu, hr₁], by linarith only [hl, hl₂]⟩

theorem nearChartBox_sound {P : Prism} (h : dataOK P = true) {v : TC.V4} (hv : v ∈ P.vertices)
    {j : Fin 3} {a₁ a₂ b₁ b₂ : ℕ} {a b : ℝ}
    (hbox : nearChartBox P j a₁ a₂ b₁ b₂ = true)
    (ha : a ∈ Icc (a₁:ℝ) a₂) (hb : b ∈ Icc (b₁:ℝ) b₂) :
    (v.v3 = 0 ∧ isConeBox P j.val a₂ b₁ b₂ = true) ∨
      WeightedRow criticalQ (Tangent.vertex P.profileDen v) (realPi P) (realInput P v)
        (Tangent.chartRow j (Tangent.chartCoord ctx a) (Tangent.chartCoord ctx b)) := by
  simp only [nearChartBox, Bool.and_eq_true] at hbox
  obtain ⟨⟨ha', hb'⟩, hchecks⟩ := hbox
  have hg := List.all_eq_true.mp hchecks v hv
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hg
  rcases hg with hg | hg
  · exact Or.inl hg
  right
  obtain ⟨hsA, hr, hapos, haabs⟩ := nearAxis_sound ha' ha
  obtain ⟨hsB, hs, hbpos, hbabs⟩ := nearAxis_sound hb' hb
  let r := nearAnchor a₁ a₂
  let s := nearAnchor b₁ b₂
  have hq : 1 ≤ criticalQ := (by norm_num : (1:ℝ) ≤ 1054/665).trans criticalQ_bracket.1.le
  have hm := chartCoord_mono (C := ctx)
  have ha' : Tangent.chartCoord ctx a ∈ Icc (Tangent.chartCoord ctx a₁) (Tangent.chartCoord ctx a₂) :=
    ⟨hm ha.1, hm ha.2⟩
  have hb' : Tangent.chartCoord ctx b ∈ Icc (Tangent.chartCoord ctx b₁) (Tangent.chartCoord ctx b₂) :=
    ⟨hm hb.1, hm hb.2⟩
  have hA := nearTangent_le_rpow (r := r) hr hapos haabs
  have hB := nearTangent_le_rpow (r := s) hs hbpos hbabs
  simp only [sub_eq_add_neg, ← neg_mul] at hA hB
  refine Tangent.weightedRow_of_signed_rectangle hq (realPi_nonneg P) (realInput_nonneg h hv)
    j ha' hb' hsA hsB hA hB ?_
  simp only [nearBox, Bool.and_eq_true] at hg
  intro A hAm B hBm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hAm hBm
  rcases hAm with rfl | rfl <;> rcases hBm with rfl | rfl
  · simpa only [sub_eq_add_neg, ← neg_mul] using nearCorner_sound h hg.1.1.1
  · simpa only [sub_eq_add_neg, ← neg_mul] using nearCorner_sound h hg.1.1.2
  · simpa only [sub_eq_add_neg, ← neg_mul] using nearCorner_sound h hg.1.2
  · simpa only [sub_eq_add_neg, ← neg_mul] using nearCorner_sound h hg.2

end HlawkaSchatten.BelowExponent.FacetNumeric
