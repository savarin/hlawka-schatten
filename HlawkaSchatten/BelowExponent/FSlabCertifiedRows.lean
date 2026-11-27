/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabTaylorSound
import all HlawkaSchatten.BelowExponent.Tangent.Rectangle
import all HlawkaSchatten.BelowExponent.FacetArchive.NearChecker
import Batteries.Tactic.OpenPrivate

/-! Every real row in a checked F band is covered by a certified leaf. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FSlabCheck

open Set Tangent
open FacetNumeric (ctx RowTree numericBoxOK isConeBox isConeBox_sound facetRowTangent_le nearAxis
  nearAnchor nearIntercept nearSlope nearTangent_le_rpow)
open private chartCoord_mono chartCoord_signed from HlawkaSchatten.BelowExponent.Tangent.Rectangle
open private nearAxis_sound from HlawkaSchatten.BelowExponent.FacetArchive.NearChecker

private def Leaf (P : Band) (j : Fin 3) (a₀ a₁ b₀ b₁ : ℕ) : Prop :=
  ∃ ca cb, leafOK P j (face P j) ca cb a₀ a₁ b₀ b₁ = true

private theorem checkCover (P : Band) (j : Fin 3) {tree : RowTree} {a₀ a₁ b₀ b₁ : ℕ}
    (h : checkTree P j (face P j) tree a₀ a₁ b₀ b₁ = true) : TC.BoxCover (Leaf P j) a₀ a₁ b₀ b₁ := by
  induction tree generalizing a₀ a₁ b₀ b₁ with
  | box ca cb => exact .leaf ⟨ca,cb,h⟩
  | splitA left right ih₀ ih₁ =>
    simp only [checkTree, Bool.and_eq_true, TC.blt_true, and_assoc] at h
    exact .splitA _ h.1.le h.2.1.le (ih₀ h.2.2.1) (ih₁ h.2.2.2)
  | splitB left right ih₀ ih₁ =>
    simp only [checkTree, Bool.and_eq_true, TC.blt_true, and_assoc] at h
    exact .splitB _ h.1.le h.2.1.le (ih₀ h.2.2.1) (ih₁ h.2.2.2)

private theorem physicalRectangle (P : Band) (hW : P.weight ≤ 100) (j : Fin 3)
    {a₀ a₁ b₀ b₁ : ℕ} {A B ca da cb db : ℝ}
    (ha : A ∈ Icc (a₀:ℝ) a₁) (hb : B ∈ Icc (b₀:ℝ) b₁)
    (hsa : 0 ≤ chartCoord ctx a₀ ∨ chartCoord ctx a₁ ≤ 0)
    (hsb : 0 ≤ chartCoord ctx b₀ ∨ chartCoord ctx b₁ ≤ 0)
    (hA : ca+da*|chartCoord ctx A| ≤ |chartCoord ctx A|^criticalQ)
    (hB : cb+db*|chartCoord ctx B| ≤ |chartCoord ctx B|^criticalQ)
    (i : Fin 3)
    (hcorners : ∀ a ∈ ({a₀,a₁} : Set ℕ), ∀ b ∈ ({b₀,b₁} : Set ℕ),
      fPairOutput (len P) (mu P) (imbalanceAt P false) (imbalanceAt P true) i
        (chartRow j (chartCoord ctx a) (chartCoord ctx b)) ≤
      cornerInput (fDoubleGamma (mu P) (len P)) j (fun x => ca+da*|x|) (fun x => cb+db*|x|)
        (chartCoord ctx a) (chartCoord ctx b)) :
    fPairOutput (len P) (mu P) (imbalanceAt P false) (imbalanceAt P true) i
      (chartRow j (chartCoord ctx A) (chartCoord ctx B)) ≤
    ∑ k, fDoubleGamma (mu P) (len P) k*|chartRow j (chartCoord ctx A) (chartCoord ctx B) k|^criticalQ := by
  have hμ₀ : 0 ≤ mu P := by unfold mu; positivity
  have hμ₁ : mu P ≤ 1 := by
    have hw : (P.weight : ℝ) ≤ 100 := by exact_mod_cast hW
    unfold mu
    linarith only [hw]
  have hg (k : Fin 3) : 0 ≤ fDoubleGamma (mu P) (len P) k := by
    unfold fDoubleGamma
    have hr := fSlabKnot_bounds P.knot
    have hL : (74/4096:ℝ) ≤ len P := by
      rw [len_eq]
      simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hr.1
    have hU : len P ≤ (7/125:ℝ) := by
      rw [len_eq]
      simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hr.2
    exact mul_nonneg (by norm_num) (balancedGamma_nonneg hμ₀ hμ₁ (by linarith) (by linarith) k)
  have hm := chartCoord_mono (C := ctx)
  refine fRows_of_signed_rectangle (fPairOutput_convex hμ₀ hμ₁ (imbalanceAt_bound P false)
    (imbalanceAt_bound P true) i) hg j ⟨hm ha.1,hm ha.2⟩ ⟨hm hb.1,hm hb.2⟩ hsa hsb hA hB ?_
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hcorners a₀ (by simp) b₀ (by simp)
  · exact hcorners a₀ (by simp) b₁ (by simp)
  · exact hcorners a₁ (by simp) b₀ (by simp)
  · exact hcorners a₁ (by simp) b₁ (by simp)

set_option maxHeartbeats 600000 in
theorem fBandRows_of_checked (P : Band) (hW : P.weight ≤ 100) (trees : Fin 3 → RowTree)
    (hcharts : ∀ j, checkChart P j (trees j) = true) :
    FBandRows (len P) (mu P) (imbalanceAt P false) (imbalanceAt P true) := by
  intro j a b ha hb hOutside i
  have hD : 0 < ctx.Da := by decide
  obtain ⟨A,hA,ha'⟩ := signed_coord_to_offset hD ha
  obtain ⟨B,hB,hb'⟩ := signed_coord_to_offset hD hb
  rw [← ha', ← hb'] at hOutside ⊢
  have hA' : A ∈ Icc ((0:ℕ):ℝ) ((2*ctx.Da:ℕ):ℝ) := by push_cast; exact hA
  have hB' : B ∈ Icc ((0:ℕ):ℝ) ((2*ctx.Da:ℕ):ℝ) := by push_cast; exact hB
  obtain ⟨a₀,a₁,b₀,b₁,⟨ca,cb,hleaf⟩,haLoc,hbLoc⟩ :=
    exists_leaf_at (checkCover P j (hcharts j)) hA' hB'
  unfold leafOK at hleaf
  split at hleaf
  · have hc := isConeBox_sound radius (by decide) hleaf hA.1 hB.1 hB.2 haLoc.2 hbLoc.1 hbLoc.2
    exact False.elim (hOutside (by simpa only [radius,Nat.cast_ofNat,Nat.cast_one,chartCoord,
      FacetNumeric.chartRow,Tangent.chartRow] using hc))
  split at hleaf
  · simp only [nearCorners,Bool.and_eq_true] at hleaf
    obtain ⟨hsa, hr, hposA, hmagA⟩ := nearAxis_sound hleaf.1.1 haLoc
    obtain ⟨hsb, hs, hposB, hmagB⟩ := nearAxis_sound hleaf.1.2 hbLoc
    have haT := nearTangent_le_rpow hr hposA hmagA
    have hbT := nearTangent_le_rpow hs hposB hmagB
    simp only [sub_eq_add_neg, ← neg_mul] at haT hbT
    refine physicalRectangle P hW j haLoc hbLoc hsa hsb haT hbT i ?_
    have hcs := List.all_eq_true.mp hleaf.2 i (List.mem_finRange _)
    simp only [Bool.and_eq_true] at hcs
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha,hb]
    · simpa only [sub_eq_add_neg, ← neg_mul] using
        nearGroup_sound P hW j a₀ b₀ (nearAnchor a₀ a₁) (nearAnchor b₀ b₁) i hcs.1.1.1
    · simpa only [sub_eq_add_neg, ← neg_mul] using
        nearGroup_sound P hW j a₀ b₁ (nearAnchor a₀ a₁) (nearAnchor b₀ b₁) i hcs.1.1.2
    · simpa only [sub_eq_add_neg, ← neg_mul] using
        nearGroup_sound P hW j a₁ b₀ (nearAnchor a₀ a₁) (nearAnchor b₀ b₁) i hcs.1.2
    · simpa only [sub_eq_add_neg, ← neg_mul] using
        nearGroup_sound P hW j a₁ b₁ (nearAnchor a₀ a₁) (nearAnchor b₀ b₁) i hcs.2
  · obtain ⟨hsa,hsb,h00,h01,h10,h11⟩ := TC.leafOK_spec _ _ _ _ _ _ _ _ _ _ _ _ hleaf
    have hEq (k : ℕ) (x : ℝ) : rowTangent ctx k x =
      -(↑(TC.acoef ctx k).1:ℝ)/(2:ℝ)^ctx.K + (↑(TC.acoef ctx k).2:ℝ)/(2:ℝ)^ctx.K*|x| := by
      unfold rowTangent
      rw [add_div,mul_div_right_comm]
    refine physicalRectangle P hW j haLoc hbLoc (chartCoord_signed hD hsa)
      (chartCoord_signed hD hsb) (hEq ca _ ▸ facetRowTangent_le ca _) (hEq cb _ ▸ facetRowTangent_le cb _) i ?_
    have hcs := fCornerSound P hW j
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha,hb]
    · simpa only [← hEq] using hcs ca cb a₀ b₀ h00 i
    · simpa only [← hEq] using hcs ca cb a₀ b₁ h01 i
    · simpa only [← hEq] using hcs ca cb a₁ b₀ h10 i
    · simpa only [← hEq] using hcs ca cb a₁ b₁ h11 i

end HlawkaSchatten.BelowExponent.FSlabCheck
