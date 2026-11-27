/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.IntervalJets

/-! Enclose the parameter coordinates and the three factors of each fifth root. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

local notation "pt" => DyadicBounds.point

namespace DyadicBounds

theorem sumThree_mem {f : Fin 3 → DyadicBounds} {v : Row} (h : ∀ i, (f i).Contains (v i)) :
    (sumThree f).Contains (∑ i, v i) := by
  rw [Fin.sum_univ_three]
  exact ((h 0).add (h 1)).add (h 2)

theorem zero_mem : (point 0).Contains (0 : ℝ) := by simpa only [Rat.cast_zero] using point_mem 0

theorem one_mem : (point 1).Contains (1 : ℝ) := by simpa only [Rat.cast_one] using point_mem 1

theorem two_mem : (point 2).Contains (2 : ℝ) := by simpa only [Rat.cast_ofNat] using point_mem 2

end DyadicBounds

@[simp] theorem axisSlopeRat_cast (k i : Fin 3) : (axisSlopeRat k i : ℝ) = axisSlope k i := by
  by_cases h : i = k <;> simp [axisSlopeRat, axisSlope, h]

@[simp] theorem directionSlopeRat_cast (k i : Fin 3) : (directionSlopeRat k i : ℝ) = directionSlope k i := by
  fin_cases i <;> simp [directionSlopeRat, directionSlope]

theorem ParameterCell.coordinateInterval_mem {c : ParameterCell} {a b η : ℝ}
    (ht : c.Contains a b η) (k i : Fin 3) : (coordinateInterval c k i).Contains (coordinateJet k ![a, b, η] i) := by
  have h (i : Fin 3) : (![c.a, c.b, c.η] i).Contains (![a, b, η] i) := by
    fin_cases i
    · exact ht.first
    · exact ht.second
    · exact ht.eta
  have hf : (pt (axisSlopeRat k i)).Contains (axisSlope k i) := by
    simpa only [axisSlopeRat_cast] using DyadicBounds.point_mem (axisSlopeRat k i)
  exact ⟨DyadicBounds.ofRat_mem (h i), hf, DyadicBounds.zero_mem⟩

theorem ParameterCell.directionInterval_mem {c : ParameterCell} {a b η : ℝ}
    (ht : c.Contains a b η) (k i : Fin 3) : (directionInterval c k i).Contains (directionJet k ![a, b, η] i) := by
  have hf : (pt (directionSlopeRat k i)).Contains (directionSlope k i) := by
    simpa only [directionSlopeRat_cast] using DyadicBounds.point_mem (directionSlopeRat k i)
  exact ⟨DyadicBounds.ofRat_mem (ParameterCell.direction_mem ht i), hf, DyadicBounds.zero_mem⟩

theorem ParameterCell.ratioInterval_mem {c : ParameterCell} {a b η : ℝ}
    (ht : c.Contains a b η) (k : Fin 3) (m : ℚ) :
    let n := 1 + (m : ℝ) * η
    let t := axisSlope k 2
    (ratioInterval c k m).Contains ⟨η / n, t / n^2, (-2 * (m : ℝ) * t) / (n^2 * n)⟩ := by
  intro n t
  have hη := DyadicBounds.ofRat_mem ht.eta
  have hn : ((pt 1).add ((pt m).mul (DyadicBounds.ofRat c.η))).Contains n :=
    DyadicBounds.one_mem.add ((DyadicBounds.point_mem m).mul hη)
  have ht' : (pt (axisSlopeRat k 2)).Contains t := by
    simpa only [t, axisSlopeRat_cast] using DyadicBounds.point_mem (axisSlopeRat k 2)
  have hc : (pt (-2 * m)).Contains (-2 * (m : ℝ)) := by
    simpa using DyadicBounds.point_mem (-2 * m)
  exact ⟨hη.div hn, ht'.div hn.square, (hc.mul ht').div (hn.square.mul hn)⟩

theorem ParameterCell.depthInterval_mem {c : ParameterCell} {a b η : ℝ}
    (ht : c.Contains a b η) (k : Fin 3) : (depthInterval c k).Contains (depthJet k ![a, b, η]) := by
  simpa [depthInterval, depthJet, pow_succ _ 2, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using
    ParameterCell.ratioInterval_mem ht k 2

theorem ParameterCell.etaRatioInterval_mem {c : ParameterCell} {a b η : ℝ}
    (ht : c.Contains a b η) (hη : 0 ≤ η) (k : Fin 3) : (etaRatioInterval c k).Contains (etaRatioJet k ![a, b, η]) := by
  rw [etaRatioJet_eq _ _ hη]
  simpa [etaRatioInterval] using ParameterCell.ratioInterval_mem ht k 1

theorem ParameterCell.radicalBaseInterval_mem {c : ParameterCell} {a b η : ℝ}
    (ht : c.Contains a b η) (k j : Fin 3) :
    (radicalBaseInterval c k j).Contains (radicalBaseJet k ![a, b, η] j) := by
  let e := parameterDirection a b
  let v := directionSlope k
  have he (i : Fin 3) : (directionInterval c k i).value.Contains (e i) :=
    (ParameterCell.directionInterval_mem ht k i).1
  have hv (i : Fin 3) : (directionInterval c k i).first.Contains (v i) :=
    (ParameterCell.directionInterval_mem ht k i).2.1
  have hε := ParameterCell.depthInterval_mem ht k
  have hOne := DyadicBounds.one_mem
  have hTwo := DyadicBounds.two_mem
  have ha := hOne.sub (he j)
  have hb := (he (j + 1)).mul (he (j + 2))
  have hbp := ((hv (j + 1)).mul (he (j + 2))).add ((he (j + 1)).mul (hv (j + 2)))
  have hneg : ((pt 0).sub (directionInterval c k j).first).Contains (-v j) := by
    simpa only [zero_sub] using DyadicBounds.zero_mem.sub (hv j)
  refine ⟨((hOne.sub hε.1).mul ha).add (hε.1.mul hb), ?_, ?_⟩
  · exact (hneg.add (hε.2.1.mul (hb.sub ha))).add (hε.1.mul (hbp.add (hv j)))
  · exact ((hε.2.2.mul (hb.sub ha)).add ((hTwo.mul hε.2.1).mul (hbp.add (hv j)))).add
      (((hTwo.mul hε.1).mul (hv (j + 1))).mul (hv (j + 2)))

theorem ParameterCell.radicalOtherInterval_mem {c : ParameterCell} {a b η : ℝ}
    (ht : c.Contains a b η) (k j : Fin 3) :
    (radicalOtherInterval c k j).Contains (radicalOtherJet k ![a, b, η] j) := by
  have he := ParameterCell.directionInterval_mem ht k j
  have hε := ParameterCell.depthInterval_mem ht k
  have h₀ := DyadicBounds.zero_mem
  have h₂ := DyadicBounds.two_mem
  refine ⟨DyadicBounds.one_mem.sub (hε.1.mul he.1), ?_, ?_⟩
  · simpa only [radicalOtherInterval, radicalOtherJet, directionJet, zero_sub] using
      ((h₀.sub hε.2.1).mul he.1).sub (hε.1.mul he.2.1)
  · simpa only [radicalOtherInterval, radicalOtherJet, directionJet, zero_sub] using
      ((h₀.sub hε.2.2).mul he.1).sub ((h₂.mul hε.2.1).mul he.2.1)

theorem ParameterCell.radicalSigmaInterval_mem {c : ParameterCell} {a b η : ℝ}
    (ht : c.Contains a b η) (k : Fin 3) :
    (radicalSigmaInterval c k).Contains (radicalSigmaJet k ![a, b, η]) := by
  have he (i : Fin 3) := (ParameterCell.directionInterval_mem ht k i).1
  have hv (i : Fin 3) := (ParameterCell.directionInterval_mem ht k i).2.1
  have h₀ := DyadicBounds.zero_mem
  refine ⟨(((he 0).mul (he 1)).add ((he 0).mul (he 2))).add ((he 1).mul (he 2)), ?_, ?_⟩
  · simpa only [radicalSigmaInterval, radicalSigmaJet, directionJet, zero_sub] using
      h₀.sub (DyadicBounds.sumThree_mem (fun i => (he i).mul (hv i)))
  · simpa only [radicalSigmaInterval, radicalSigmaJet, directionJet, zero_sub] using
      h₀.sub (DyadicBounds.sumThree_mem (fun i => (hv i).square))

end HlawkaSchatten.BelowExponent.Vertex
