/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FSlabCertifiedRows
public import HlawkaSchatten.BelowExponent.G1Complete

/-! Assemble the closed F endpoint bands into the entire ordered F strip. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FSlabCheck

open FacetNumeric (RowTree)

def endpointBand (i : Fin 156) (cap high : Bool) : Band :=
  ⟨if cap then i.succ else i.castSucc, fSlabWeightNum i, high⟩

def HasCheckedCharts (P : Band) : Prop :=
  ∃ trees : Fin 3 → RowTree, ∀ j, checkChart P j (trees j) = true

theorem checkedOfCharts {P : Band} {a b c : RowTree}
    (ha : checkChart P 0 a = true) (hb : checkChart P 1 b = true) (hc : checkChart P 2 c = true) :
    HasCheckedCharts P := by
  refine ⟨![a,b,c], ?_⟩
  intro j
  fin_cases j
  · exact ha
  · exact hb
  · exact hc

def SlabChecked (i : Fin 156) : Prop :=
  ∀ cap high, HasCheckedCharts (endpointBand i cap high)

theorem endpoints_of_checked (checked : ∀ i, SlabChecked i) :
    FSlabEndpoints (fun i => (fSlabWeight i : ℝ)) := by
  intro i cap e p s z he₀ he₁
  let K := if cap then i.succ else i.castSucc
  let l := (fSlabKnot K : ℝ)
  let μ := (fSlabWeight i : ℝ)
  have hL := fSlabKnot_bounds K
  have hl₀ : 74/4096 ≤ l := by
    have hh := (Rat.cast_le (K := ℝ)).2 hL.1
    simpa [l] using hh
  have hl₁ : l ≤ 7/125 := by
    have hh := (Rat.cast_le (K := ℝ)).2 hL.2
    simpa [l] using hh
  have hw := fSlabWeight_bounds i cap
  have hm₀ : 21/100 ≤ μ := by
    have hh := (Rat.cast_le (K := ℝ)).2 hw.1
    simpa [μ] using hh
  have hm₁ : μ ≤ 27/100 := by
    have hh := (Rat.cast_le (K := ℝ)).2 hw.2.1
    simpa [μ] using hh
  have hml : 37/200 ≤ μ-l := by
    have hh := (Rat.cast_le (K := ℝ)).2 hw.2.2
    simpa [μ,l,K] using hh
  have hedges (high : Bool) : FBandRows l μ (if high then 1/4 else 0) (if high then 1/2 else 1/4) := by
    obtain ⟨trees, ht⟩ := checked i cap high
    let P := endpointBand i cap high
    have hRows := fBandRows_of_checked P (show P.weight ≤ 100 from fSlabWeightNum_le i) trees ht
    have hl : len P = l := len_eq P
    have hm : mu P = μ := by simp [mu,P,endpointBand,μ,fSlabWeight]
    have hlow : imbalanceAt P false = if high then 1/4 else 0 := imbalanceAt_low P
    have hhigh : imbalanceAt P true = if high then 1/2 else 1/4 := imbalanceAt_high P
    rwa [hl,hm,hlow,hhigh] at hRows
  apply (weightedRow_balancedFacet_iff criticalQ μ l e p s z).1
  rcases le_total e (1/4:ℝ) with he | he
  · exact weightedRow_fBand hl₀ hl₁ hm₀ hm₁ hml le_rfl (by norm_num) he₀ he (hedges false) _
  · exact weightedRow_fBand hl₀ hl₁ hm₀ hm₁ hml (by norm_num) le_rfl he he₁ (hedges true) _

theorem rowAt_facetStrip_of_scheduled_checks (checked : ∀ i, SlabChecked i)
    {t : Profile} (ht : OrderedInterior t) (hf₀ : 1/64 ≤ facetCoord t) (hf₁ : facetCoord t ≤ 1/20)
    (hτ : tau t ≤ 3/4) (hd : t 3 ≤ 1/400) : RowAt criticalQ t := by
  apply rowAt_facetStrip_of_fSlabEndpoints (fun _ ht => rowAt_g1 ht)
    (fun i => (fSlabWeight i : ℝ)) _ (endpoints_of_checked checked) ht hf₀ hf₁ hτ hd
  intro i
  have hb := fSlabWeight_bounds i false
  have hlo : (21/100:ℝ) ≤ (fSlabWeight i : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).2 hb.1
  have hhi : (fSlabWeight i : ℝ) ≤ (27/100:ℝ) := by simpa using (Rat.cast_le (K := ℝ)).2 hb.2.1
  exact ⟨by linarith only [hlo], by linarith only [hhi]⟩

end HlawkaSchatten.BelowExponent.FSlabCheck
