/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetTangent
public import HlawkaSchatten.BelowExponent.FacetPrismCover

/-! Join the facet cone and the numeric real row estimates on a G2 prism. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public section

namespace HlawkaSchatten.BelowExponent

theorem rowAt_g2_prism_of_numeric_rows
    {P : FacetNumeric.Prism} {b : Fin 3 → Row} {π : Profile} {slope w : Row} {ρ d : ℝ}
    (hvertex : ∀ i cap,
      FacetNumeric.realVertex P i cap = facetCap (b i) (if cap then 1 / 500 else 0))
    (hprob : FacetNumeric.realPi P = π)
    (hweights : ∀ i cap, FacetNumeric.realGamma P i cap =
      prismWeight π slope (facetCap (b i) (if cap then 1 / 500 else 0)))
    (hπ : IsSimplex π)
    (hγ : ∀ i (cap : Bool) j,
      0 ≤ prismWeight π slope (facetCap (b i) (if cap then 1 / 500 else 0)) j)
    (hbudget : ∀ i (cap : Bool),
      (∑ j, prismWeight π slope (facetCap (b i) (if cap then 1 / 500 else 0)) j) ≤ 1)
    (hcone : ∀ i x, FacetRatioCone ρ x →
      WeightedRow criticalQ (facetBase (b i)) π (facetWeight π (b i)) x)
    (hnumeric : ∀ (i : Fin 3) (cap : Bool) (x : Row),
      (cap = true ∨ ¬ FacetRatioCone ρ x) →
      WeightedRow criticalQ (FacetNumeric.realVertex P i cap) (FacetNumeric.realPi P)
        (FacetNumeric.realGamma P i cap) x)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hd₀ : 0 ≤ d) (hd : d ≤ 1 / 500) :
    RowAt criticalQ (facetCap (fun j => ∑ i, w i * b i j) d) := by
  apply rowAt_facet_prism facetCritical_one_lt.le (by norm_num : 0 < (1 / 500 : ℝ))
    hd₀ hd hw hsum hπ hγ hbudget
  intro i cap x
  cases cap
  · by_cases hx : FacetRatioCone ρ x
    · have hb : facetCap (b i) 0 = facetBase (b i) := by
        funext s
        fin_cases s <;> simp [facetCap, facetBase]
      have hg : prismWeight π slope (facetCap (b i) 0) = facetWeight π (b i) := by
        funext j
        fin_cases j <;> simp [prismWeight, facetWeight, facetCap, Fin.castSucc]
      change WeightedRow criticalQ (facetCap (b i) 0) π (prismWeight π slope (facetCap (b i) 0)) x
      rw [hg, hb]
      exact hcone i x hx
    · simpa only [hvertex, hprob, hweights] using hnumeric i false x (Or.inr hx)
  · simpa only [hvertex, hprob, hweights] using hnumeric i true x (Or.inl rfl)

end HlawkaSchatten.BelowExponent
