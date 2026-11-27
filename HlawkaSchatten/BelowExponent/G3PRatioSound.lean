/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData
public import HlawkaSchatten.BelowExponent.G3PFarTilesSound

/-! Soundness of the normalized far coordinate on the central G3 chart. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

open Vertex (RatBounds)

noncomputable section

theorem ratioZ_eq {l s a z : ℝ} (hl : l < 1)
    (hc : balancedFarCenter l l 1 z = s * a) :
    z = 1 + (s * a - 1) * (1 / (1 - l)) := by
  change (1-l)*z + l*1 = s*a at hc
  field_simp [sub_ne_zero.mpr hl.ne']
  nlinarith only [hc]

theorem ratioCenter_mem {B : Box} {b : Bool} {u a : ℝ}
    (hu : (bounds B 2).Contains u) (ha : (bounds B 3).Contains a) :
    (ratioCenterBounds B b).Contains (signed b u * a) := by
  have hc := RatBounds.mul_mem (RatBounds.mul_mem (point_has (signRat b)) hu) ha
  cases b <;> simpa [ratioCenterBounds, signRat, signed] using hc

theorem ratioPhysicalBox_mem {B : Box} {b : Bool} {h σ u a z : ℝ}
    (hx : B.Mem ![h,σ,u,a]) (hσ : B.hi 1 ≤ 1/5) (hL : (lBounds B).hi < 1)
    (hc : balancedFarCenter (h*(σ/(2-σ))) (h*(σ/(2-σ))) 1 z = signed b u * a) :
    (ratioPhysicalBox B b).Mem ![h,σ,u,z] := by
  have hOne : (point 1).Contains (1 : ℝ) := by simpa using point_has 1
  have hH : (bounds B 0).Contains h := hx 0
  have hS : (bounds B 1).Contains σ := hx 1
  have hU : (bounds B 2).Contains u := hx 2
  have hA : (bounds B 3).Contains a := hx 3
  have hl : (lBounds B).Contains (h*(σ/(2-σ))) := RatBounds.mul_mem hH (k_mem hS hσ)
  have hl1 : ((lBounds B).hi : ℝ) < 1 := by exact_mod_cast hL
  have hn : (0 : ℝ) < (((point 1).sub (lBounds B)).lo : ℝ) := by
    change 0 < (((1 : ℚ) - (lBounds B).hi : ℚ) : ℝ)
    exact_mod_cast sub_pos.mpr hL
  have hZ : (ratioZBounds B b).Contains z := by
    rw [ratioZ_eq (hl.2.trans_lt hl1) hc]
    exact RatBounds.add_mem hOne (RatBounds.mul_mem
      (RatBounds.sub_mem (ratioCenter_mem hU hA) hOne)
      (recip_mem (RatBounds.sub_mem hOne hl) hn))
  intro j
  fin_cases j
  · exact hH
  · exact hS
  · exact hU
  · exact hZ

theorem RatioChart.sound {B : Box} {t : RatioChart} (b : Bool) (ht : t.ok B b = true)
    {h σ u a z : ℝ} (hx : B.Mem ![h,σ,u,a]) (hh : 0 < h) (hσ : 0 < σ) (hσ₁ : σ ≤ 1/5)
    (hCap : h ≤ 1/(2-σ/(2-σ))) (hu : 0 < u) (hz : |z| ≤ 8)
    (hc : balancedFarCenter (h*(σ/(2-σ))) (h*(σ/(2-σ))) 1 z = signed b u * a) :
    0 ≤ g3FacetGap h σ 1 (signed b u) z := by
  induction t generalizing B with
  | original t =>
    obtain ⟨hg, check⟩ := Bool.and_eq_true_iff.mp ht
    obtain ⟨hs, hl⟩ := of_decide_eq_true hg
    exact certTree_sound b (CertTree.ok_of_commonOK check)
      (ratioPhysicalBox_mem hx hs hl hc) hh hσ hσ₁ hCap hu.le hz
  | row w =>
    obtain ⟨hg, check⟩ := Bool.and_eq_true_iff.mp ht
    obtain ⟨hs, hl⟩ := of_decide_eq_true hg
    have hs' : signed b u ≠ 0 := by cases b <;> simp [signed, hu.ne']
    apply TiledRow.soundOnRatio b check (ratioPhysicalBox_mem hx hs hl hc) hh hz hu
    rw [(div_eq_iff hs').2 (hc.trans (mul_comm _ _))]
    exact hx 3
  | cut j m l r left right =>
    obtain ⟨p, q⟩ := Bool.and_eq_true_iff.mp ht
    rcases le_total (![h,σ,u,a] j) (m : ℝ) with below | above
    · exact left p (Box.mem_lower hx below)
    · exact right q (Box.mem_upper hx above)

theorem RatioRemainder.sound {B : Box} {t : RatioRemainder} (b : Bool) {cap : ℚ}
    (hcap : 0 ≤ cap) (ht : t.ok B b cap = true) {h σ u z : ℝ}
    (hx : B.Mem ![h,σ,u,z]) (hh : 0 < h) (hσ : 0 < σ) (hσ₁ : σ ≤ 1/5)
    (hCap : h ≤ 1/(2-σ/(2-σ))) (hu : 0 ≤ u) (hz : |z| ≤ 8)
    (chart : ∀ a : ℝ, |a| ≤ (cap : ℝ) → 0 < u →
      balancedFarCenter (h*(σ/(2-σ))) (h*(σ/(2-σ))) 1 z = signed b u * a →
      0 ≤ g3FacetGap h σ 1 (signed b u) z) : 0 ≤ g3FacetGap h σ 1 (signed b u) z := by
  induction t generalizing B with
  | original t => exact certTree_sound b (CertTree.ok_of_commonOK ht) hx hh hσ hσ₁ hCap hu hz
  | covered =>
    obtain ⟨ulo, slim, llim, bound⟩ := of_decide_eq_true ht
    have hH : (bounds B 0).Contains h := hx 0
    have hS : (bounds B 1).Contains σ := hx 1
    have hU : (bounds B 2).Contains u := hx 2
    have hZ : (bounds B 3).Contains z := hx 3
    have hu' : 0 < u := (show (0 : ℝ) < B.lo 2 by exact_mod_cast ulo).trans_le hU.1
    have hs : signed b u ≠ 0 := by cases b <;> simp [signed, hu'.ne']
    have hl := RatBounds.mul_mem hH (k_mem hS slim)
    have hC := center_mem hl (hl.2.trans (by exact_mod_cast llim)) hZ
    let C := balancedFarCenter (h*(σ/(2-σ))) (h*(σ/(2-σ))) 1 z
    have hC' : |C| ≤ (cap : ℝ) * u :=
      (abs_mem hC).2.trans ((show ((absBounds (center B)).hi : ℝ) ≤ (cap : ℝ) * B.lo 2 by
        exact_mod_cast bound).trans (mul_le_mul_of_nonneg_left hU.1 (by exact_mod_cast hcap)))
    refine chart (C / signed b u) ?_ hu' ?_
    · rw [abs_div, signed_abs b hu]
      exact (div_le_iff₀ hu').2 hC'
    · change C = signed b u * (C / signed b u)
      field_simp [hs]
  | cut j m l r left right =>
    obtain ⟨p,q⟩ := Bool.and_eq_true_iff.mp ht
    rcases le_total (![h,σ,u,z] j) (m : ℝ) with below | above
    · exact left p (Box.mem_lower hx below)
    · exact right q (Box.mem_upper hx above)

theorem ratioUnion_sound {B : Box} {c : RatioChart} {r : RatioRemainder} (b : Bool) {cap : ℚ}
    (hcap : 0 ≤ cap) (hc : c.ok (ratioCoverBox B cap) b = true) (hr : r.ok B b cap = true)
    {h σ u z : ℝ} (hx : B.Mem ![h,σ,u,z]) (hh : 0 < h) (hσ : 0 < σ) (hσ₁ : σ ≤ 1/5)
    (hCap : h ≤ 1/(2-σ/(2-σ))) (hu : 0 ≤ u) (hz : |z| ≤ 8) :
    0 ≤ g3FacetGap h σ 1 (signed b u) z := by
  apply r.sound b hcap hr hx hh hσ hσ₁ hCap hu hz
  intro a ha hu' heq
  apply c.sound b hc (h := h) (σ := σ) (u := u) (a := a) _ hh hσ hσ₁ hCap hu' hz heq
  intro j
  fin_cases j
  · exact hx 0
  · exact hx 1
  · exact hx 2
  · simpa [ratioCoverBox] using abs_le.mp ha

/-- A signed physical-box conclusion, independent of the certificate representation. -/
def SignedBoxGap (B : Box) (b : Bool) : Prop :=
  ∀ {h σ u z : ℝ}, B.Mem ![h,σ,u,z] → 0 < h → 0 < σ → σ ≤ 1/5 →
    h ≤ 1/(2-σ/(2-σ)) → 0 ≤ u → |z| ≤ 8 →
    0 ≤ g3FacetGap h σ 1 (signed b u) z

theorem signedGap_of_commonOK {B : Box} {t : CertTree} (b : Bool)
    (ht : t.commonOK B b = true) : SignedBoxGap B b := by
  intro h σ u z hx hh hσ hσ₁ hCap hu hz
  exact certTree_sound b (CertTree.ok_of_commonOK ht) hx hh hσ hσ₁ hCap hu hz

theorem ratioUnion_signedGap {B : Box} {c : RatioChart} {r : RatioRemainder} (b : Bool)
    {cap : ℚ} (hcap : 0 ≤ cap) (hc : c.ok (ratioCoverBox B cap) b = true)
    (hr : r.ok B b cap = true) : SignedBoxGap B b := by
  intro h σ u z hx hh hσ hσ₁ hCap hu hz
  exact ratioUnion_sound b hcap hc hr hx hh hσ hσ₁ hCap hu hz

/-- Join signed conclusions on the same closed box, retaining the zero row. -/
theorem signed_box_pair {h₀ h₁ σ₀ σ₁ : ℚ}
    (hPos : SignedBoxGap ⟨![h₀, σ₀, 0, -8], ![h₁, σ₁, 1, 8]⟩ true)
    (hNeg : SignedBoxGap ⟨![h₀, σ₀, 0, -8], ![h₁, σ₁, 1, 8]⟩ false)
    {h σ s z : ℝ} (hh : 0 < h) (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1 / 5)
    (hh₁ : h ≤ 1 / (2 - σ / (2 - σ))) (hs : |s| ≤ 1) (hz : |z| ≤ 8)
    (hH₀ : (h₀ : ℝ) ≤ h) (hH₁ : h ≤ (h₁ : ℝ))
    (hS₀ : (σ₀ : ℝ) ≤ σ) (hS₁ : σ ≤ (σ₁ : ℝ)) : 0 ≤ g3FacetGap h σ 1 s z := by
  have hx : (⟨![h₀, σ₀, 0, -8], ![h₁, σ₁, 1, 8]⟩ : Box).Mem ![h, σ, |s|, z] := by
    intro i
    fin_cases i
    · exact ⟨hH₀, hH₁⟩
    · exact ⟨hS₀, hS₁⟩
    · simpa using And.intro (abs_nonneg s) hs
    · simpa using abs_le.mp hz
  rcases le_total 0 s with hsgn | hsgn
  · simpa [signed, abs_of_nonneg hsgn] using
      hPos hx hh hσ₀ hσ₁ hh₁ (abs_nonneg s) hz
  · simpa [signed, abs_of_nonpos hsgn] using
      hNeg hx hh hσ₀ hσ₁ hh₁ (abs_nonneg s) hz

end

end HlawkaSchatten.BelowExponent.G3P
