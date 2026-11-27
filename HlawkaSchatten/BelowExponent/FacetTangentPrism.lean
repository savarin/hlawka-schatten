/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetTangent
public import HlawkaSchatten.BelowExponent.FacetPrismCover

/-! Assemble a depth-1/400 facet prism from its exact tangent and base-cone certificates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.FacetNumeric

theorem facetCap_at_zero (b : Row) : facetCap b 0 = facetBase b := by
  funext j
  fin_cases j <;> simp [facetCap, facetBase]

private theorem prismWeight_base (π : Profile) (slope b : Row) :
    prismWeight π slope (facetBase b) = facetWeight π b := by
  have heq (i : Fin 3) : facetBase b i.castSucc = b i := by
    fin_cases i <;> rfl
  funext j
  simp only [prismWeight, heq, show facetBase b 3 = 0 from rfl, mul_zero, add_zero]

theorem rowAt_facetPrism_of_tangents {P : Prism} {b : Fin 3 → Row} {π : Profile} {slope α : Row}
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
    (hcharts : ∀ j : Fin 3, checkChart P j.val (Tangent.chartA j).val (Tangent.chartB j).val (trees j) = true)
    (htan : ∀ code x, Tangent.rowTangent ctx code x ≤ |x| ^ criticalQ)
    (hcorners : PrismCornerSound P) : RowAt criticalQ (facetCap (fun j => ∑ i, α i * b i j) d) := by
  apply rowAt_facet_prism facetCritical_one_lt.le (by norm_num : 0 < (1/400 : ℝ)) hd₀ hd₁ hα hαsum hπ
    (fun i cap => (hbudget i cap).1) (fun i cap => (hbudget i cap).2)
  have hr := prismRows_of_numeric h trees hcharts htan hcorners
  have hbase : ∀ v cap, (vertexAt P v cap).v3 = 0 → ∀ x,
      FacetRatioCone ((P.radiusNum : ℝ) / P.radiusDen) x →
      WeightedRow criticalQ (realVertex P v cap) (realPi P) (realGamma P v cap) x := by
    intro v cap hz x hc
    cases cap
    · rw [hvertex, hweight, hinput]
      simp only [Bool.false_eq_true, ↓reduceIte, facetCap_at_zero, prismWeight_base]
      exact hcone v x hc
    · exact False.elim (hcap v hz)
  intro v cap x
  simpa only [hvertex, hweight, hinput] using hr hbase v cap x

end HlawkaSchatten.BelowExponent.FacetNumeric
