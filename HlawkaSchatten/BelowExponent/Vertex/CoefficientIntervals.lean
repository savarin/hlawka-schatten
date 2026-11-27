/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.RadicalIntervals

/-! Rational interval transport through the beta, normalized weight and curvature formulas. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

private theorem betaNumeratorInterval_mem {c : ParameterCell} {a b η : ℝ} (ht : c.Contains a b η)
    (hη : 0 ≤ η) (k : Fin 3) (i : Fin 4) :
    (betaNumeratorInterval c k i).Contains (betaNumeratorJet k ![a,b,η] i) := by
  have e (j) := ParameterCell.directionInterval_mem ht k j
  have h : (betaCoordinateInterval c k i).Contains (betaCoordinateJet k ![a,b,η] i) := by
    fin_cases i
    · change (IntervalJet.const 1).Contains (Jet.const 1)
      simpa only [Rat.cast_one] using IntervalJet.const_mem 1
    · exact (e 0).div (e 1)
    · exact (e 0).div (e 2)
    · exact (e 0).mul (ParameterCell.etaRatioInterval_mem ht hη k)
  exact h.mul h

private theorem betaDenInterval_mem {c : ParameterCell} {a b η : ℝ} (ht : c.Contains a b η)
    (hη : 0 ≤ η) (k : Fin 3) : (betaDenInterval c k).Contains (betaDenJet k ![a,b,η]) := by
  have h (i) := betaNumeratorInterval_mem ht hη k i
  exact (((h 0).add (h 1)).add (h 2)).add (h 3)

theorem betaInterval_mem {c : ParameterCell} {a b η : ℝ} (ht : c.Contains a b η)
    (hη : 0 ≤ η) (k j : Fin 3) : (betaInterval c k j).Contains (betaJet k ![a,b,η] j) :=
  (betaNumeratorInterval_mem ht hη k j.castSucc).div (betaDenInterval_mem ht hη k)

theorem betaHeavyInterval_mem {c : ParameterCell} {a b η : ℝ} (ht : c.Contains a b η)
    (hη : 0 ≤ η) (k : Fin 3) : (betaHeavyInterval c k).Contains (betaHeavyJet k ![a,b,η]) := by
  have h₁ : (IntervalJet.const 1).Contains (Jet.const 1) := by simpa only [Rat.cast_one] using IntervalJet.const_mem 1
  have h := (ParameterCell.directionInterval_mem ht k 0).mul (h₁.add (ParameterCell.etaRatioInterval_mem ht hη k))
  exact (h.mul h).div (betaDenInterval_mem ht hη k)

theorem vector_get_ofFn {α : Type} {n : ℕ} (f : Fin n → α) : (Vector.ofFn f).get = f :=
  funext fun i => Vector.getElem_ofFn (f := f) i.isLt

private theorem complementInterval_mem {c : ParameterCell} {a b η : ℝ} (ht : c.Contains a b η) (k i : Fin 3) :
    (complementInterval c k i).Contains (complementJet k ![a,b,η] i) := by
  have h₁ : (IntervalJet.const 1).Contains (Jet.const 1) := by simpa only [Rat.cast_one] using IntervalJet.const_mem 1
  exact h₁.sub (ParameterCell.directionInterval_mem ht k i)

private theorem signedRadicalInterval_mem {c : ParameterCell} {roots : Fin 3 → RatBounds} {p : Row} (k j : Fin 3)
    (hR : ∀ i, (radicalInterval c roots k i).Contains (radicalJet k p i)) :
    (signedRadicalInterval (radicalInterval c roots k) j).Contains (signedRadicalJet k p j) := by
  unfold signedRadicalInterval signedRadicalJet
  refine IntervalJet.sumThree_mem ?_
  intro i
  have hcast : ((if i = j then (-1 : ℚ) else 1 : ℚ) : ℝ) = (if i = j then -1 else 1) := by
    by_cases h : i = j <;> simp [h]
  exact hcast ▸ (hR i).scale (if i = j then -1 else 1)

private theorem sharedCoefficientInterval_mem {c : ParameterCell} {roots : Fin 3 → RatBounds}
    {a b η : ℝ} (ht : c.Contains a b η) (hη : 0 ≤ η) (k : Fin 3)
    (hR : ∀ i, (radicalInterval c roots k i).Contains (radicalJet k ![a,b,η] i)) :
    (sharedCoefficientInterval (depthInterval c k) (betaHeavyInterval c k) (radicalInterval c roots k)
      (signedRadicalInterval (radicalInterval c roots k)) (betaInterval c k) (directionInterval c k)).Contains
      (sharedCoefficientJet k ![a,b,η]) := by
  have hε := ParameterCell.depthInterval_mem ht k
  have hbh := betaHeavyInterval_mem ht hη k
  have h₁ : (IntervalJet.const 1).Contains (Jet.const 1) := by simpa only [Rat.cast_one] using IntervalJet.const_mem 1
  have hT := IntervalJet.sumThree_mem hR
  have hf := (((hε.mul hbh).mul (h₁.sub hε)).mul (hT.sub hε)).scale (2 / 3)
  have hn := IntervalJet.sumThree_mem fun i =>
    (((betaInterval_mem ht hη k i).mul (ParameterCell.directionInterval_mem ht k i)).mul
      (hε.add (signedRadicalInterval_mem k i hR))).scale (2 / 3)
  simpa only [sharedCoefficientInterval, sharedCoefficientJet, Rat.cast_div, Rat.cast_ofNat] using hf.add hn

theorem parameterDInterval_mem {c : ParameterCell} {roots : Fin 3 → RatBounds} {a b η : ℝ}
    (ht : c.Contains a b η) (hη : 0 ≤ η) (k j : Fin 3)
    (hR : ∀ i, (radicalInterval c roots k i).Contains (radicalJet k ![a,b,η] i)) :
    ((axisCoefficientIntervals c roots k).d.get j).Contains (parameterDJet k ![a,b,η] j) := by
  have hε := ParameterCell.depthInterval_mem ht k
  have ha := complementInterval_mem ht k j
  have hb (i) := betaInterval_mem ht hη k i
  have hbh := betaHeavyInterval_mem ht hη k
  have h₁ : (IntervalJet.const 1).Contains (Jet.const 1) := by simpa only [Rat.cast_one] using IntervalJet.const_mem 1
  have hm := h₁.sub (hε.mul ha)
  have hf := hm.mul (h₁.sub ((hb j).scale 2))
  have hs := ha.mul (signedRadicalInterval_mem k j hR)
  have hthird := (((hε.mul hbh).mul (hR j)).mul hm).scale (-2)
  have hfourth := (ha.mul (((hb (j+1)).mul (hR (j+2))).add ((hb (j+2)).mul (hR (j+1))))).scale (-2)
  simp only [axisCoefficientIntervals, axisCoefficientsFromRadicals, vector_get_ofFn, dInterval, parameterDJet]
  simpa only [Rat.cast_ofNat, Rat.cast_neg] using
    (((hf.add hs).add hthird).add hfourth).add (sharedCoefficientInterval_mem ht hη k hR)

theorem parameterWeightInterval_mem {c : ParameterCell} {roots : Fin 3 → RatBounds} {a b η : ℝ}
    (ht : c.Contains a b η) (hη : 0 ≤ η) (k j : Fin 3)
    (hR : ∀ i, (radicalInterval c roots k i).Contains (radicalJet k ![a,b,η] i)) :
    ((axisCoefficientIntervals c roots k).weight.get j).Contains (parameterWeightJet k ![a,b,η] j) := by
  have hε := ParameterCell.coordinateInterval_mem ht k 2
  have h₁ : (IntervalJet.const 1).Contains (Jet.const 1) := by simpa only [Rat.cast_one] using IntervalJet.const_mem 1
  have hn := h₁.add (hε.scale 2)
  simpa only [axisCoefficientIntervals, axisCoefficientsFromRadicals, vector_get_ofFn,
    parameterWeightJet, normalizerJet, Rat.cast_ofNat] using
    (hn.mul (hR j)).add (hε.mul (parameterDInterval_mem ht hη k j hR))

theorem parameterHInterval_mem {c : ParameterCell} {roots : Fin 3 → RatBounds} {a b η : ℝ}
    (ht : c.Contains a b η) (hη : 0 ≤ η) (k i j : Fin 3)
    (hR : ∀ s, (radicalInterval c roots k s).Contains (radicalJet k ![a,b,η] s)) :
    (((axisCoefficientIntervals c roots k).h.get i).get j).Contains (parameterHJet k ![a,b,η] i j) := by
  simpa only [axisCoefficientIntervals, axisCoefficientsFromRadicals, vector_get_ofFn, parameterHJet] using
    (complementInterval_mem ht k i).mul (parameterWeightInterval_mem ht hη k j hR)

end HlawkaSchatten.BelowExponent.Vertex
