/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1CompactDataCore
public import HlawkaSchatten.BelowExponent.BulkGrid
import HlawkaSchatten.BelowExponent.G1CompactSlabs.Slab00
import HlawkaSchatten.BelowExponent.G1CompactSlabs.Slab01
import HlawkaSchatten.BelowExponent.G1CompactSlabs.Slab02
import HlawkaSchatten.BelowExponent.G1CompactSlabs.Slab03
import HlawkaSchatten.BelowExponent.G1CompactSlabs.Slab04
import HlawkaSchatten.BelowExponent.G1CompactSlabs.Slab05
import HlawkaSchatten.BelowExponent.G1CompactSlabs.Slab06
import HlawkaSchatten.BelowExponent.G1CompactSlabs.Slab07
import HlawkaSchatten.BelowExponent.G1CompactSlabs.Slab08
import HlawkaSchatten.BelowExponent.G1CompactSlabs.Slab09
import HlawkaSchatten.BelowExponent.G1CompactSlabs.Slab10
import HlawkaSchatten.BelowExponent.G1CompactSlabs.Slab11
import HlawkaSchatten.BelowExponent.G1CompactSlabs.Slab12

/-! Recombine the compact G1 slab checks and derive the real row bound. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

open Set

open G1CompactData

set_option maxRecDepth 16000

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem compactBasicChecks (i : Fin 13) :
    ∀ right j, compactBasicOK i right j := by
  fin_cases i <;> decide +kernel

private theorem compactCornerChecks (i : Fin 13) :
    ∀ right j, compactCornersOK i right j := by
  fin_cases i
  · exact compactCornerChecks00
  · exact compactCornerChecks01
  · exact compactCornerChecks02
  · exact compactCornerChecks03
  · exact compactCornerChecks04
  · exact compactCornerChecks05
  · exact compactCornerChecks06
  · exact compactCornerChecks07
  · exact compactCornerChecks08
  · exact compactCornerChecks09
  · exact compactCornerChecks10
  · exact compactCornerChecks11
  · exact compactCornerChecks12

private theorem qLo_le : (qLo : ℝ) ≤ criticalQ := by
  exact (by norm_num [qLo] : (qLo : ℝ) ≤ 1054/665).trans criticalQ_bracket.1.le

private theorem qHi_ge : criticalQ ≤ (qHi : ℝ) := by
  exact criticalQ_bracket.2.le.trans (by norm_num [qHi])

private theorem q_one : 1 ≤ criticalQ :=
  (by norm_num [qLo] : (1:ℝ) ≤ (qLo:ℝ)).trans qLo_le

private theorem midpoint_sound (j : Fin 128) :
    0 < (G1CompactData.midpoint j : ℝ) ∧
      ((midBounds j).1 : ℝ)/powerScale ≤ (G1CompactData.midpoint j : ℝ)^criticalQ ∧
      (G1CompactData.midpoint j : ℝ)^criticalQ ≤ ((midBounds j).2 : ℝ)/powerScale := by
  obtain ⟨⟨hm, hm₁⟩, _, hLo, hHi⟩ := midpointChecks j
  have hp : 0 < (G1CompactData.midpoint j : ℝ) := by
    unfold G1CompactData.midpoint
    push_cast
    exact div_pos (by exact_mod_cast hm) (by norm_num)
  have hle : (G1CompactData.midpoint j : ℝ) ≤ 1 := by
    unfold G1CompactData.midpoint
    push_cast
    exact (div_le_one₀ (by norm_num : (0:ℝ) < 512)).mpr (by exact_mod_cast hm₁)
  have hL := (le_natRat_rpow_iff (a := midpointNum j) (m := 65) (n := 41)
    (by decide : 0 < (512:ℕ)) (by decide : 0 < powerScale) (by decide)).mpr hLo
  have hU := (natRat_rpow_le_iff (a := midpointNum j) (m := 84) (n := 53)
    (by decide : 0 < (512:ℕ)) (by decide : 0 < powerScale) (by decide)).mpr hHi
  have hpt : (G1CompactData.midpoint j : ℝ) = (midpointNum j : ℝ)/512 := by unfold G1CompactData.midpoint; push_cast; rfl
  simp only [Nat.cast_ofNat] at hL hU
  rw [← hpt] at hL hU
  refine ⟨hp, hL.trans ?_, ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_ge hp hle (by simpa [qHi] using qHi_ge)
  · exact (Real.rpow_le_rpow_of_exponent_ge hp hle (by simpa [qLo] using qLo_le)).trans hU

private theorem tangentEndpoint_sound (j : Fin 128) (right : Bool) :
    (ordinate (centerNode j right) : ℝ) ≤ (G1CompactData.midpoint j : ℝ)^criticalQ *
      (1+criticalQ*(|(knot (centerNode j right) : ℝ)|/(G1CompactData.midpoint j : ℝ)-1)) := by
  let f := tangentFactor j right
  let d := tangentOffset j right
  have htest' : tangentTest j right := by
    cases right
    · exact (tangentChecks j).1
    · exact (tangentChecks j).2
  have htestR := (Rat.cast_le (K := ℝ)).mpr htest'
  change (ordinate (centerNode j right) : ℝ) ≤
    (((tangentPower j right : ℚ)/powerScale*f : ℚ) : ℝ) at htestR
  push_cast at htestR
  have hr : (d : ℝ) = |(knot (centerNode j right) : ℝ)|/(G1CompactData.midpoint j : ℝ)-1 := by
    dsimp [d, tangentOffset]
    push_cast
    rfl
  have hfactor : (f : ℝ) ≤ 1+criticalQ*(d:ℝ) := by
    change ((1+(if 0 ≤ d then qLo else qHi)*d : ℚ) : ℝ) ≤ _
    by_cases hd : 0 ≤ d
    · rw [ite_eq_left hd]
      push_cast
      linarith only [mul_le_mul_of_nonneg_right qLo_le (by exact_mod_cast hd : 0 ≤ (d:ℝ))]
    · rw [ite_eq_right hd]
      push_cast
      linarith only [mul_le_mul_of_nonpos_right qHi_ge
        (by exact_mod_cast (le_of_not_ge hd) : (d:ℝ) ≤ 0)]
  refine htestR.trans ?_
  unfold tangentPower
  calc
    _ ≤ (G1CompactData.midpoint j : ℝ)^criticalQ * (f:ℝ) := by
      by_cases hf : 0 ≤ f
      · rw [ite_eq_left hf]
        exact mul_le_mul_of_nonneg_right (midpoint_sound j).2.1 (by exact_mod_cast hf)
      · rw [ite_eq_right hf]
        exact mul_le_mul_of_nonpos_right (midpoint_sound j).2.2
          (by exact_mod_cast (le_of_not_ge hf))
    _ ≤ _ := hr ▸ mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg (midpoint_sound j).1.le _)

private theorem compact_ordinate_lerp (j : Fin 128) {u : ℝ} (hu : u ∈ Icc 0 1) :
    (1-u)*(ordinate j.castSucc : ℝ) + u*(ordinate j.succ : ℝ) ≤
      |(1-u)*(knot j.castSucc : ℝ) + u*(knot j.succ : ℝ)|^criticalQ := by
  have hsign := (midpointChecks j).2.1
  refine signed_tangent_segment_lower q_one (midpoint_sound j).1 hu ?_ ?_ ?_
  · rcases hsign with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩
    · exact Or.inr ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩
  · exact tangentEndpoint_sound j false
  · exact tangentEndpoint_sound j true

private theorem compactParams_radius_cast (i : Fin 13) (right : Bool) (j : Fin 64) :
    ((compactParams i right j).w : ℝ) =
      ((compactWitness i right j).2.1 : ℝ)/16384 := by
  change (( ((compactWitness i right j).2.1 : ℚ)/wScale : ℚ) : ℝ) = _
  push_cast
  rfl

private theorem compactParams_length_cast (i : Fin 13) (right : Bool) (j : Fin 64) :
    ((compactParams i right j).l : ℝ) = (lengthNum i right : ℝ)/4096 := by
  change (((lengthNum i right : ℚ)/4096 : ℚ) : ℝ) = _
  push_cast
  rfl

private theorem knot_cast (j : Fin 129) : (knot j : ℝ) = (knotNum j : ℝ)/256 := by
  unfold knot
  push_cast
  rfl

private theorem compactOverlap_sound (i : Fin 13) (right : Bool) (j : Fin 64)
    (k : Fin 128) {z : ℝ} (ha : (knot k.castSucc : ℝ) ≤ z) (hb : z ≤ (knot k.succ : ℝ))
    (hZ : |(1-(compactParams i right j).l : ℝ)*z+(compactParams i right j).l| ≤
      ((compactParams i right j).w : ℝ)) :
    overlapsCompact (lengthNum i right) (compactWitness i right j).2.1 k := by
  let l := ((compactParams i right j).l : ℝ)
  let w := ((compactParams i right j).w : ℝ)
  have hlR : l < 1 := by
    dsimp [l]
    exact_mod_cast (compactBasicChecks i right j).2.1
  have hl := sub_nonneg.mpr hlR.le
  have ha' := mul_le_mul_of_nonneg_left ha hl
  have hb' := mul_le_mul_of_nonneg_left hb hl
  change |(1-l)*z+l| ≤ w at hZ
  have h₁ : -w ≤ (1-l)*(knot k.succ : ℝ)+l := by linarith only [(abs_le.mp hZ).1, hb']
  have h₂ : (1-l)*(knot k.castSucc : ℝ)+l ≤ w := by linarith only [(abs_le.mp hZ).2, ha']
  dsimp [l, w] at h₁ h₂
  rw [compactParams_length_cast, compactParams_radius_cast, knot_cast] at h₁ h₂
  have hc₁ :
      -(64 : ℝ)*((compactWitness i right j).2.1 : ℝ) ≤
        (4096-(lengthNum i right : ℝ))*(knotNum k.succ : ℝ) + 256*(lengthNum i right : ℝ) := by
    linarith only [h₁]
  have hc₂ :
      (4096-(lengthNum i right : ℝ))*(knotNum k.castSucc : ℝ) + 256*(lengthNum i right : ℝ) ≤
        (64 : ℝ)*((compactWitness i right j).2.1 : ℝ) := by
    linarith only [h₂]
  exact ⟨by exact_mod_cast hc₁, by exact_mod_cast hc₂⟩

private theorem z_in_compact_grid {l w z : ℝ} (hl : 0 ≤ l) (hl₁ : l < 1)
    (hW : w+l ≤ (1-l)/4) (hZ : |(1-l)*z+l| ≤ w) : |z| ≤ 1/4 := by
  have ha := abs_add_le ((1-l)*z+l) (-l)
  rw [show (1-l)*z+l + -l = (1-l)*z by ring, abs_neg, abs_of_nonneg hl,
    abs_mul, abs_of_nonneg (sub_nonneg.mpr hl₁.le)] at ha
  apply (mul_le_mul_iff_right₀ (sub_pos.mpr hl₁)).1
  linarith only [ha, hZ, hW]

private theorem compactCost_upper {μ l k α β : ℝ} (hK : 0 ≤ k*l^2/μ) (hA : 0 ≤ α)
    (a b u : ℝ) (hu : u ∈ Icc 0 1) :
    let f := fun z : ℝ => k*l^2/μ*(z-1)^2+β+α*((1-l)*z+l)^2
    f ((1-u)*a+u*b) ≤ (1-u)*f a+u*f b := by
  let f := fun z : ℝ => k*l^2/μ*(z-1)^2+β+α*((1-l)*z+l)^2
  change f ((1-u)*a+u*b) ≤ (1-u)*f a+u*f b
  have h := mul_nonneg (mul_nonneg (sub_nonneg.mpr hu.2) hu.1)
    (mul_nonneg (sq_nonneg (a-b)) (add_nonneg hK (mul_nonneg hA (sq_nonneg (1-l)))))
  apply sub_nonneg.mp
  have heq : (1-u)*f a+u*f b-f ((1-u)*a+u*b) =
      (1-u)*u*((a-b)^2*(k*l^2/μ+α*(1-l)^2)) := by
    dsimp [f]
    ring
  rw [heq]
  exact h

private theorem compact_inner_bound (i : Fin 13) (right : Bool) (j : Fin 64) {z : ℝ} :
    let P := compactParams i right j
    let l : ℝ := P.l
    let μ : ℝ := P.μ
    let k : ℝ := P.k
    let β : ℝ := P.β
    let α : ℝ := P.α
    |(1-l)*z+l| ≤ (P.w : ℝ) →
      k*l^2/μ*(z-1)^2+β+α*((1-l)*z+l)^2 ≤ l+(1-l)*|z|^criticalQ := by
  let P := compactParams i right j
  let l : ℝ := P.l
  let μ : ℝ := P.μ
  let k : ℝ := P.k
  let β : ℝ := P.β
  let α : ℝ := P.α
  change |(1-l)*z+l| ≤ (P.w:ℝ) →
    k*l^2/μ*(z-1)^2+β+α*((1-l)*z+l)^2 ≤ l+(1-l)*|z|^criticalQ
  intro hz
  have hBasic := compactBasicChecks i right j
  obtain ⟨hl, hl₁, hm, _, _, _, _, _, hk, _, _, _, hw⟩ := hBasic
  have hlR : 0 ≤ l := by dsimp [l, P]; exact_mod_cast hl.le
  have hl₁R : l < 1 := by dsimp [l, P]; exact_mod_cast hl₁
  have hwR : (P.w : ℝ)+l ≤ (1-l)/4 := by dsimp [l, P]; exact_mod_cast hw
  have hb := abs_le.mp (z_in_compact_grid hlR hl₁R hwR hz)
  have h₀ : (knot 0 : ℝ) ≤ z := by
    rw [knot_cast]
    norm_num [knotNum] 
    exact hb.1
  have h₁ : z ≤ (knot (Fin.last 128) : ℝ) := by
    rw [knot_cast]
    norm_num [knotNum, Fin.last]
    exact hb.2
  obtain ⟨a, ha, hb⟩ := exists_adjacent_knots 127 (f := fun b => (knot b : ℝ)) h₀ h₁
  have hOverlap := compactOverlap_sound i right j a ha hb hz
  obtain ⟨u, hu, heq⟩ := exists_interval_lerp ha hb
  have hK : 0 ≤ k*l^2/μ := by
    have hkR : 0 ≤ k := by dsimp [k, P]; exact_mod_cast hk
    have hmR : 0 ≤ μ := by dsimp [μ, P]; exact_mod_cast hm.le
    exact div_nonneg (mul_nonneg hkR (sq_nonneg _)) hmR
  have hA : 0 ≤ α := by
    change 0 ≤ (((qHi/2)*(((compactWitness i right j).2.2 : ℚ)/powerScale) /
      ((compactWitness i right j).2.1/wScale : ℚ)^2 : ℚ) : ℝ)
    push_cast
    unfold qHi
    push_cast
    positivity
  have hcorner (b : Bool) :
      k*l^2/μ*((knot (centerNode a b) : ℝ)-1)^2+β+
        α*((1-l)*(knot (centerNode a b) : ℝ)+l)^2 ≤ l+(1-l)*(ordinate (centerNode a b) : ℝ) := by
    have hRat := (Rat.cast_le (K := ℝ)).mpr (compactCornerChecks i right j a hOverlap b)
    change ((compactCost P (knot (centerNode a b)) : ℚ) : ℝ) ≤ _ at hRat
    unfold compactCost at hRat
    push_cast at hRat
    exact hRat
  have ht := compact_ordinate_lerp a hu
  have h₁ := mul_le_mul_of_nonneg_left (hcorner false) (sub_nonneg.mpr hu.2)
  have h₂ := mul_le_mul_of_nonneg_left (hcorner true) hu.1
  change _ ≤ _ at h₁ h₂
  simp only [centerNode, Bool.false_eq_true, ite_false, ite_true] at h₁ h₂
  rw [heq]
  refine (compactCost_upper hK hA _ _ _ hu).trans ?_
  have hin := mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr hl₁R.le)
  linarith only [h₁, h₂, hin]

end HlawkaSchatten.BelowExponent
