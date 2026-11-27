/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.FacetPrism

/-! Interpolate the common-weight certificate from the six prism vertices. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public section

namespace HlawkaSchatten.BelowExponent

/-- Three base and three cap certificates close the prism, including its end faces. -/
theorem rowAt_facet_prism {q D d : ℝ} {b : Fin 3 → Row} {π : Profile} {slope α : Row}
    (hq : 1 ≤ q) (hD : 0 < D) (hd₀ : 0 ≤ d) (hdD : d ≤ D)
    (hα : ∀ i, 0 ≤ α i) (hαsum : ∑ i, α i = 1) (hπ : IsSimplex π)
    (hγ : ∀ i (cap : Bool) j,
      0 ≤ prismWeight π slope (facetCap (b i) (if cap then D else 0)) j)
    (hbudget : ∀ i (cap : Bool),
      (∑ j, prismWeight π slope (facetCap (b i) (if cap then D else 0)) j) ≤ 1)
    (hvertex : ∀ i (cap : Bool) (x : Row),
      WeightedRow q (facetCap (b i) (if cap then D else 0)) π
        (prismWeight π slope (facetCap (b i) (if cap then D else 0))) x) :
    RowAt q (facetCap (fun j => ∑ i, α i * b i j) d) := by
  let u := d / D
  have hu₀ : 0 ≤ u := div_nonneg hd₀ hD.le
  have hu₁ : u ≤ 1 := (div_le_one₀ hD).2 hdD
  have hd : u * D = d := div_mul_cancel₀ _ hD.ne'
  let w (i : Fin 3 × Bool) : ℝ := α i.1 * (if i.2 then u else 1 - u)
  let v (i : Fin 3 × Bool) : Profile := facetCap (b i.1) (if i.2 then D else 0)
  have hw (i : Fin 3 × Bool) : 0 ≤ w i := by
    refine mul_nonneg (hα i.1) ?_
    split
    · exact hu₀
    · exact sub_nonneg.mpr hu₁
  have hsumPair (i : Fin 3) : (∑ cap : Bool, w (i, cap)) = α i := by
    simp [w]
    ring
  have hsum : ∑ i, w i = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [hsumPair]
    exact hαsum
  have hvPair (i : Fin 3) :
      (∑ cap : Bool, w (i, cap) • v (i, cap)) = α i • facetCap (b i) d := by
    funext s
    rw [Fintype.sum_bool]
    rw [← hd]
    fin_cases s <;> simp [w, v, facetCap, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  have hsumV : ∑ i, w i • v i = facetCap (fun j => ∑ i, α i * b i j) d := by
    rw [Fintype.sum_prod_type]
    simp_rw [hvPair]
    funext s
    fin_cases s <;>
      simp [facetCap, Finset.sum_apply, smul_eq_mul, ← Finset.sum_mul, hαsum,
        Finset.mul_sum, mul_left_comm]
  rw [← hsumV]
  exact rowAt_barycenter hq (fun i _ => hw i) hsum hπ (fun i _ => hγ i.1 i.2)
    (fun i _ => hbudget i.1 i.2) (fun i _ => hvertex i.1 i.2)

end HlawkaSchatten.BelowExponent
