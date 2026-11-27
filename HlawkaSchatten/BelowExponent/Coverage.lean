/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! The eleven regions `InRegion` cover the ordered open simplex. The theorem
`ordered_mem_region` assigns every ordered profile in the interior to at least one region. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable section

structure OrderedInterior (t : Profile) : Prop where
  simplex : IsSimplex t
  last_pos : 0 < t 3
  first_ge : t 1 ≤ t 0
  second_ge : t 2 ≤ t 1
  third_ge : t 3 ≤ t 2

abbrev edgeMass (t : Profile) := t 2 + t 3
abbrev vertexDepth (t : Profile) := 1 - t 0
abbrev tau (t : Profile) := t 0 / (t 0 + t 1)
abbrev sigma (t : Profile) := edgeMass t / vertexDepth t
abbrev facetCoord (t : Profile) := t 2 / (1 - t 3)
abbrev minDirection (t : Profile) := t 3 / vertexDepth t
abbrev maxDirection (t : Profile) := t 1 / vertexDepth t
abbrev imbalance (t : Profile) := t 0 - t 1
abbrev cornerH (t : Profile) := 1 - imbalance t
abbrev cornerK (t : Profile) := sigma t / (2 - sigma t)

/-- Hypotheses of the individual certificates, always used at an ordered interior point. -/
inductive InRegion (t : Profile) : Prop
  | bulk (hd : 1/500 ≤ t 3)
  | facetInterior (hd : t 3 ≤ 1/500) (hf : 1/20 ≤ facetCoord t)
  | edgeJunction (hl : edgeMass t ≤ 1/4000) (h₁ : 1/4 ≤ tau t) (h₂ : tau t ≤ 3/4)
  | balancedEdge (hl₁ : 1/4096 ≤ edgeMass t) (hl₂ : edgeMass t ≤ 74/4096)
      (he₁ : 0 ≤ imbalance t) (he₂ : imbalance t ≤ 1/2)
  | facetStrip (hf₁ : 1/64 ≤ facetCoord t) (hf₂ : facetCoord t ≤ 1/20)
      (hτ₁ : 1/4 ≤ tau t) (hτ₂ : tau t ≤ 3/4) (hd : t 3 ≤ 1/400) (hs : 8*t 3 ≤ t 2)
  | deepFacet (hd : t 3 ≤ 1/500) (hf : facetCoord t ≤ 1/20)
      (hε : 1/8 ≤ vertexDepth t) (hσ : 1/5 ≤ sigma t) (hτ : 3/4 ≤ tau t)
  | vertexMiddle (hm : 1/20 ≤ minDirection t) (hM : maxDirection t ≤ 4/5)
      (hε : vertexDepth t ≤ 1/20)
  | vertexBand (hm₁ : 1/40 ≤ minDirection t) (hm₂ : minDirection t ≤ 1/20)
      (hM : maxDirection t ≤ 4/5) (hε : vertexDepth t ≤ 1/12)
  | vertexSide (hm : minDirection t ≤ 1/40) (hM : maxDirection t ≤ 4/5)
      (hε : vertexDepth t ≤ 1/8)
  | vertexEdge (hσ : sigma t ≤ 7/10000) (hε : vertexDepth t ≤ 13/50)
  | vertexCorner (hσ₁ : 7/10000 ≤ sigma t) (hσ₂ : sigma t ≤ 1/5)
      (hh₁ : 0 < cornerH t) (hh₂ : cornerH t ≤ 1/(2 - cornerK t))

theorem OrderedInterior.sum_four {t : Profile} (ht : OrderedInterior t) :
    t 0 + t 1 + t 2 + t 3 = 1 := by
  have hs := ht.simplex.2
  simp [Fin.sum_univ_succ] at hs
  linarith

theorem OrderedInterior.depth_pos {t : Profile} (ht : OrderedInterior t) : 0 < vertexDepth t := by
  change 0 < 1 - t 0
  linarith [ht.sum_four, ht.last_pos, ht.third_ge, ht.second_ge]

theorem OrderedInterior.maxDirection_eq {t : Profile} (ht : OrderedInterior t) :
    maxDirection t = 1 - sigma t := by
  change t 1 / vertexDepth t = 1 - (t 2 + t 3) / vertexDepth t
  field_simp [ht.depth_pos.ne']
  linarith [ht.sum_four]

/-- In particular all three row charts in the corner use the same split parameter. -/
theorem OrderedInterior.depth_mul_ratio {t : Profile} (ht : OrderedInterior t)
    (hσ : sigma t ≤ 1/5) : cornerH t * cornerK t = edgeMass t := by
  have hv : sigma t * vertexDepth t = edgeMass t := div_mul_cancel₀ _ ht.depth_pos.ne'
  have hh : cornerH t = vertexDepth t * (2 - sigma t) := by
    change 1 - (t 0 - t 1) = vertexDepth t * (2 - sigma t)
    rw [mul_sub, mul_comm (vertexDepth t) (sigma t), hv]
    unfold vertexDepth edgeMass
    linarith [ht.sum_four]
  have hn : 2 - sigma t ≠ 0 := by linarith
  change cornerH t * (sigma t / (2 - sigma t)) = edgeMass t
  rw [hh, ← hv]
  field_simp [hn]

/-- Every ordered interior profile belongs to a region with a written row certificate. -/
theorem ordered_mem_region {t : Profile} (ht : OrderedInterior t) : InRegion t := by
  have hs := ht.sum_four
  have hd := ht.last_pos
  have hc := ht.third_ge
  have hb := ht.second_ge
  have ha := ht.first_ge
  have he := ht.depth_pos
  have hab : 0 < t 0 + t 1 := by linarith
  have hden : 0 < 1 - t 3 := by linarith
  have hτmin : 1/4 ≤ tau t := (le_div_iff₀ hab).2 (by linarith)
  by_cases hbulk : 1/500 ≤ t 3
  · exact .bulk hbulk
  by_cases hfacet : 1/20 ≤ facetCoord t
  · exact .facetInterior (le_of_not_ge hbulk) hfacet
  have hdsmall := le_of_not_ge hbulk
  have hfsmall := le_of_not_ge hfacet
  by_cases hτ : tau t ≤ 3/4
  · have hlin := (div_le_iff₀ hab).1 hτ
    by_cases hnear : edgeMass t ≤ 1/4000
    · exact .edgeJunction hnear hτmin hτ
    by_cases hwide : edgeMass t ≤ 74/4096
    · exact .balancedEdge (by linarith) hwide (sub_nonneg.mpr ha) (by
        unfold imbalance
        linarith)
    have hsub : t 2 ≤ facetCoord t := (le_div_iff₀ hden).2 (by
      nlinarith [mul_nonneg (le_trans hd.le hc) hd.le])
    unfold edgeMass at hwide
    exact .facetStrip (by linarith) hfsmall hτmin hτ (by linarith) (by linarith)
  have hτ' := (lt_div_iff₀ hab).1 (lt_of_not_ge hτ)
  by_cases hσ : 1/5 ≤ sigma t
  · by_cases hdeep : 1/8 ≤ vertexDepth t
    · exact .deepFacet hdsmall hfsmall hdeep hσ (le_of_not_ge hτ)
    have hM : maxDirection t ≤ 4/5 := by rw [ht.maxDirection_eq]; linarith
    by_cases hm : 1/20 ≤ minDirection t
    · have hr := (le_div_iff₀ he).1 hm
      exact .vertexMiddle hm hM (by linarith)
    by_cases hn : 1/40 ≤ minDirection t
    · have hr := (le_div_iff₀ he).1 hn
      exact .vertexBand hn (le_of_not_ge hm) hM (by linarith)
    exact .vertexSide (le_of_not_ge hn) hM (le_of_not_ge hdeep)
  have hsl : sigma t ≤ 1/5 := le_of_not_ge hσ
  by_cases hlow : sigma t ≤ 7/10000
  · have hmass := (div_le_iff₀ he).1 hlow
    unfold edgeMass vertexDepth at hmass
    apply InRegion.vertexEdge hlow
    unfold vertexDepth
    linarith
  have hratio := ht.depth_mul_ratio hsl
  have hk : cornerK t ≤ 1/9 := (div_le_iff₀ (by linarith : 0 < 2 - sigma t)).2 (by linarith)
  refine .vertexCorner (le_of_not_ge hlow) hsl ?_ ((le_div_iff₀ (by linarith : 0 < 2 - cornerK t)).2 ?_)
  · unfold cornerH imbalance
    linarith
  · rw [mul_sub, hratio]
    unfold cornerH imbalance edgeMass
    linarith

end
end HlawkaSchatten.BelowExponent
