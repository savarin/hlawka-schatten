/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.ParameterIntervals

/-! Refine a checked parent fifth-root interval on a smaller parameter box. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

namespace DyadicBounds

theorem refinementDenominator_mem {r a : DyadicBounds} {x y : ℝ} (hr : r.Contains x) (ha : a.Contains y) :
    (refinementDenominator r a).Contains (x^4+x^3*y+x^2*y^2+x*y^3+y^4) := by
  have x₂ := hr.square
  have y₂ := ha.square
  have h := ((((x₂.square.add ((x₂.mul hr).mul ha)).add (x₂.mul y₂)).add ((hr.mul y₂).mul ha)).add y₂.square)
  rw [show x^4+x^3*y+x^2*y^2+x*y^3+y^4 =
    (x^2)^2 + (x^2*x)*y + x^2*y^2 + (x*y^2)*y + (y^2)^2 by ring]
  exact h

theorem refineRadical_mem {r power : DyadicBounds} {x : ℝ} (hr : r.Contains x)
    (hpower : power.Contains (x^5)) (hx : 0 ≤ x) : (refineRadical r power).Contains x := by
  intro hok
  let m := (r.lo + r.hi) / 2
  let a := ofNumerator m
  let v := decode m
  obtain ⟨hb, hm⟩ := Bool.and_eq_true_iff.mp hok
  have hv : 0 < v := decode_pos (show 0 < m from of_decide_eq_true hm)
  have ha : a.Contains v := numerator_mem m
  have ha₅ : (a.square.square.mul a).Contains (v^5) := by
    convert ha.square.square.mul ha using 1
    ring
  have hnext : (a.add ((power.sub (a.square.square.mul a)).div (refinementDenominator r a))).Contains x := by
    have hs := ha.add ((hpower.sub ha₅).div (refinementDenominator_mem hr ha))
    rwa [← fifth_refinement hx hv (rfl : x^5 = x^5)] at hs
  exact (hr.intersect hnext) hb

end DyadicBounds

theorem radicalPowerInterval_mem {a b s : IntervalJet} {A B S : Jet}
    (ha : a.Contains A) (hb : b.Contains B) (hs : s.Contains S) :
    (radicalPowerInterval a b s).Contains (A.value^2*B.value^3/S.value^2) := by
  rw [show A.value^2*B.value^3 = (A.value^2*B.value^2)*B.value by ring]
  exact ((ha.1.square.mul hb.1.square).mul hb.1).div hs.1.square

/-- All three refinements use the parent proof and exact rational arithmetic. -/
theorem ParameterCell.radicalInterval_mem {c parent : ParameterCell} {roots : Fin 3 → RatBounds}
    {a b η : ℝ} (hc : c.Contains a b η) (hp : parent.Contains a b η)
    (hroot : parent.rootsOK roots = true) (k j : Fin 3) :
    (radicalInterval c roots k j).Contains (radicalJet k ![a,b,η] j) := by
  let ε := η/(1+2*η)
  let e := parameterDirection a b
  let R := radical ε e j
  have hgate := hroot
  simp only [ParameterCell.rootsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hgate
  obtain ⟨_, Hb, _⟩ := ParameterCell.radical_factors_mem hgate.1 hp j
  have hBounds := hgate.2 j (by simp)
  simp only [rootBoundsOK, decide_eq_true_eq] at hBounds
  have hb₀ : (0 : ℝ) ≤ (parent.other j).lo := by exact_mod_cast hBounds.2.1
  have hb₁ := hb₀.trans Hb.1
  have hpow₀ : 0 ≤ radicand ε e j := by
    exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hb₁ 3)) (sq_nonneg _)
  have hR : 0 ≤ R := Real.rpow_nonneg hpow₀ _
  have hPow : R^5 = radicand ε e j := radical_fifth hpow₀
  have hA := ParameterCell.radicalBaseInterval_mem hc k j
  have hB := ParameterCell.radicalOtherInterval_mem hc k j
  have hS := ParameterCell.radicalSigmaInterval_mem hc k
  have hP : (radicalPowerInterval (radicalBaseInterval c k j) (radicalOtherInterval c k j)
      (radicalSigmaInterval c k)).Contains (R^5) := by
    rw [hPow]
    exact radicalPowerInterval_mem hA hB hS
  have r₀ : (DyadicBounds.ofRat (roots j)).Contains R :=
    DyadicBounds.ofRat_mem (ParameterCell.radical_mem hroot hp j)
  have r₁ := DyadicBounds.refineRadical_mem r₀ hP hR
  have r₂ := DyadicBounds.refineRadical_mem r₁ hP hR
  have r₃ := DyadicBounds.refineRadical_mem r₂ hP hR
  exact IntervalJet.radical_mem r₃ hA hB hS

end HlawkaSchatten.BelowExponent.Vertex
