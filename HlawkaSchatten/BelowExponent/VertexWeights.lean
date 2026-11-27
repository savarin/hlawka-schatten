/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.VertexChart

/-! Explicit normalized weights used by the vertex-middle, vertex-band and vertex-side certificates.
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

noncomputable section

def cross (e : Row) (j : Fin 3) := e (j+1) * e (j+2)

def sigmaTwo (e : Row) : ℝ := e 0*e 1 + e 0*e 2 + e 1*e 2

def radicand (ε : ℝ) (e : Row) (j : Fin 3) : ℝ :=
  ((1-ε)*(1-e j) + ε*cross e j)^2 * (1-ε*e j)^3 / (sigmaTwo e)^2

def radical (ε : ℝ) (e : Row) : Row := fun j => (radicand ε e j) ^ (1/5 : ℝ)

def betaNumer (e : Row) : Row := ![1, (e 0 / e 1)^2, (e 0 / e 2)^2]

def betaDen (η : ℝ) (e : Row) : ℝ :=
  1 + (e 0 / e 1)^2 + (e 0 / e 2)^2 + (e 0 * (η/(1+η)))^2

def beta (η : ℝ) (e : Row) : Row := fun j => betaNumer e j / betaDen η e

def betaHeavy (η : ℝ) (e : Row) : ℝ := (e 0 * (1+η/(1+η)))^2 / betaDen η e

/-- d=c/λ after cancellation of the common normalizer. The formula has no inverse of e₀. -/
def coefficient (ε bh : ℝ) (e b R : Row) (j : Fin 3) : ℝ :=
  let T := ∑ i, R i
  let Δ := fun i => T-2*R i
  let X := (2/3)*(ε*bh*(1-ε)*(T-ε) + ∑ i, b i*e i*(ε+Δ i))
  let a := 1-e j
  (1-ε*a)*(1-2*b j) + a*Δ j - 2*ε*bh*R j*(1-ε*a) -
    2*a*(b (j+1)*R (j+2) + b (j+2)*R (j+1)) + X

theorem beta_sum {η ε : ℝ} (hη : 0 ≤ η) (hε : ε*(1+2*η) = η) (e : Row) :
    (∑ j, beta η e j) + ε^2 * betaHeavy η e = 1 := by
  have hn : 0 < betaDen η e := by unfold betaDen; positivity
  have hee : ε * (1+η/(1+η)) = η/(1+η) := by
    field_simp [show 1+η ≠ 0 by positivity]
    linarith only [hε]
  have hnum : ∑ j, betaNumer e j = 1+(e 0/e 1)^2+(e 0/e 2)^2 := by
    simp [Fin.sum_univ_three, betaNumer]
  have hlast : ε^2*(e 0*(1+η/(1+η)))^2 = (e 0*(η/(1+η)))^2 := by
    calc
      _ = (e 0*(ε*(1+η/(1+η))))^2 := by ring
      _ = _ := by rw [hee]
  simp only [beta, betaHeavy, ← Finset.sum_div, ← mul_div_assoc, ← add_div, hnum, hlast]
  simpa only [betaDen, mul_div_assoc] using (div_self hn.ne')

theorem coefficient_sum {ε bh : ℝ} {e b : Row} (he : ∑ j, e j = 1)
    (hb : (∑ j, b j) + ε^2 * bh = 1) (R : Row) :
    ∑ j, coefficient ε bh e b R j = 1 := by
  simp only [Fin.sum_univ_three] at he hb ⊢
  have he₂ : e 2 = 1-e 0-e 1 := by linarith
  have hb₂ : b 2 = 1-b 0-b 1-ε^2*bh := by linarith
  norm_num [coefficient, Fin.sum_univ_three, Fin.reduceAdd, he₂, hb₂]
  ring

theorem radical_fifth {ε : ℝ} {e : Row} {j : Fin 3} (hB : 0 ≤ radicand ε e j) :
    radical ε e j ^ 5 = radicand ε e j := by
  unfold radical
  rw [← Real.rpow_mul_natCast hB]
  norm_num

/-- Coordinate order agrees with the original simplex and all three shifted row outputs. -/
def directions (t : Profile) : Row := ![t 3 / vertexDepth t, t 2 / vertexDepth t, t 1 / vertexDepth t]

theorem directions_sum {t : Profile} (ht : OrderedInterior t) : ∑ j, directions t j = 1 := by
  simp [directions, Fin.sum_univ_three]
  field_simp [ht.depth_pos.ne']
  linarith only [ht.sum_four]

theorem directions_mem_unit {t : Profile} (ht : OrderedInterior t) (j : Fin 3) :
    0 ≤ directions t j ∧ directions t j ≤ 1 := by
  have hn (i : Fin 3) : 0 ≤ directions t i := by
    fin_cases i <;> exact div_nonneg (ht.simplex.1 _) ht.depth_pos.le
  have hb := Finset.single_le_sum (s := Finset.univ) (f := directions t)
    (fun i _ => hn i) (Finset.mem_univ j)
  exact ⟨hn j, hb.trans_eq (directions_sum ht)⟩

theorem radicand_nonneg {t : Profile} (ht : OrderedInterior t) (hsmall : vertexDepth t < 1/2)
    (j : Fin 3) : 0 ≤ radicand (vertexDepth t) (directions t) j := by
  have he := mul_le_mul_of_nonneg_left (directions_mem_unit ht j).2 ht.depth_pos.le
  have hc : 0 ≤ 1 - vertexDepth t * directions t j := by linarith only [he, hsmall]
  exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hc 3)) (sq_nonneg _)

theorem profile_directions {t : Profile} (ht : OrderedInterior t) :
    profile (vertexDepth t) (directions t) = t := by
  funext i
  fin_cases i <;> simp [profile, directions, vertexDepth] <;>
    rw [mul_comm, div_mul_cancel₀ _ (show 1-t 0 ≠ 0 from ht.depth_pos.ne')]

/-- Only the checked coefficient signs and the normalized gap remain as inputs.
The simplex budgets and the passage to all physical rows are discharged here. -/
theorem rowAt_of_coefficient_checks {q : ℝ} {t : Profile} (hq : 1 < q) (ht : OrderedInterior t)
    (hsmall : vertexDepth t < 1/2)
    (checked : let ε := vertexDepth t; let e := directions t; let η := ε/(1-2*ε)
     let R := radical ε e; let d := coefficient ε (betaHeavy η e) e (beta η e) R
     (∀ j, 0 ≤ rowWeight η R d j) ∧
       (∀ z : Row, |argument η e z|^q ≤ feature q η e R d z)) :
    RowAt q t := by
  let ε := vertexDepth t
  let e := directions t
  let η := ε/(1-2*ε)
  let R := radical ε e
  let d := coefficient ε (betaHeavy η e) e (beta η e) R
  change (∀ j, 0 ≤ rowWeight η R d j) ∧
    (∀ z : Row, |argument η e z|^q ≤ feature q η e R d z) at checked
  have ht₀ : 0 < 1-2*ε := by dsimp [ε]; linarith
  have hη : 0 < η := div_pos ht.depth_pos ht₀
  have hdepth : η*(1-2*ε)=ε := div_mul_cancel₀ _ ht₀.ne'
  have hε : ε*(1+2*η)=η := by linarith only [hdepth]
  have hR (j : Fin 3) : 0 ≤ R j := Real.rpow_nonneg (radicand_nonneg ht hsmall j) _
  have hd : ∑ j, d j = 1 := coefficient_sum (directions_sum ht) (beta_sum hη.le hε e) R
  have hsum : 0 ≤ ∑ j, R j := Finset.sum_nonneg fun i _ => hR i
  have hn : 0 < η+(1+2*η)*(∑ j, R j) := by positivity
  rw [← profile_directions ht]
  exact rowAt_of_normalized hq (directions_sum ht) hη.le (inv_pos.mpr hn) hdepth hR hd
    checked.1 (inv_mul_cancel₀ hn.ne') checked.2

end
end HlawkaSchatten.BelowExponent.Vertex
