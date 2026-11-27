/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeGradientIntervals
public import HlawkaSchatten.BelowExponent.Vertex.CornerCoefficientBounds

/-! Closed parameter-cell bounds for the actual normalized SC coefficients. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def RatBounds.divPositive (N D : RatBounds) : RatBounds :=
  N.mul ⟨1 / D.hi, 1 / D.lo⟩

theorem RatBounds.divPositive_mem {N D : RatBounds} {x y : ℝ}
    (hx : N.Contains x) (hy : D.Contains y) (hl : 0 < D.lo) : (N.divPositive D).Contains (x/y) := by
  have hlo : (0 : ℝ) < D.lo := by exact_mod_cast hl
  have hrec : (⟨1 / D.hi, 1 / D.lo⟩ : RatBounds).Contains (1 / y) := by
    constructor <;> push_cast
    · exact one_div_le_one_div_of_le (hlo.trans_le hy.1) hy.2
    · exact one_div_le_one_div_of_le hlo hy.1
  simpa only [RatBounds.divPositive, mul_one_div] using RatBounds.mul_mem hx hrec

def RatBounds.sideSquare (I : RatBounds) : RatBounds := I.mul I

theorem RatBounds.sideSquare_mem {I : RatBounds} {x : ℝ} (h : I.Contains x) :
    I.sideSquare.Contains (x^2) := by
  simpa only [sideSquare, pow_two] using mul_mem h h

def ParameterCell.sideEtaDen (c : ParameterCell) : RatBounds := (RatBounds.point 1).add c.η

def ParameterCell.sideEtaRatio (c : ParameterCell) : RatBounds := c.η.divPositive c.sideEtaDen

def ParameterCell.sideBetaDen (c : ParameterCell) : RatBounds :=
  let e := c.direction
  (((RatBounds.point 1).add ((e 0).divPositive (e 1)).sideSquare).add
    ((e 0).divPositive (e 2)).sideSquare).add ((e 0).mul c.sideEtaRatio).sideSquare

def ParameterCell.sideBetaFactor (c : ParameterCell) (j : Fin 3) : RatBounds :=
  ((c.direction 0).divPositive (c.direction j).sideSquare).divPositive c.sideBetaDen

def ParameterCell.sideHeavyFactor (c : ParameterCell) : RatBounds :=
  ((c.direction 0).mul ((RatBounds.point 1).add c.sideEtaRatio).sideSquare).divPositive c.sideBetaDen

def ParameterCell.sideGradient (c : ParameterCell) (roots : Fin 3 → RatBounds) : SideGradientInputs :=
  ⟨c.η, c.depth, c.direction, roots, (RatBounds.point 1).divPositive c.sideBetaDen,
    c.sideBetaFactor 1, c.sideBetaFactor 2, c.sideHeavyFactor⟩

def ParameterCell.sideGradientOK (c : ParameterCell) : Bool :=
  decide (0 < c.sideEtaDen.lo ∧ 0 < (c.direction 1).lo ∧ 0 < (c.direction 2).lo ∧
    0 < (c.direction 1).sideSquare.lo ∧ 0 < (c.direction 2).sideSquare.lo ∧ 0 < c.sideBetaDen.lo)

def DyadicBounds.toSideRat (a : DyadicBounds) : RatBounds := ⟨a.lower, a.upper⟩

theorem DyadicBounds.contains_toSideRat {a : DyadicBounds} {x : ℝ} (hx : a.Contains x)
    (hok : a.ok = true) : a.toSideRat.Contains x := by
  simpa only [RatBounds.Contains, toSideRat, lower, upper, decode, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_natCast] using hx hok

noncomputable section

theorem ParameterCell.sideGradient_sound {c : ParameterCell} {roots : Fin 3 → RatBounds}
    (hr : c.rootsOK roots = true) (hok : c.sideGradientOK = true) {a b η : ℝ}
    (h : c.Contains a b η) (j : Fin 3) :
    ((c.sideGradient roots).evaluate j).Contains
      (sideGradientFactor η (parameterDirection a b)
        (radical (η / (1 + 2 * η)) (parameterDirection a b)) j) := by
  let e := parameterDirection a b
  have one : (RatBounds.point 1).Contains (1 : ℝ) := by simpa using RatBounds.point_mem 1
  have he (i : Fin 3) := c.direction_mem h i
  obtain ⟨hDen, h₁, h₂, hs₁, hs₂, hBeta⟩ := of_decide_eq_true hok
  have hη₀ : 0 ≤ c.η.lo := by
    simp only [ParameterCell.rootsOK, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact hr.1
  have hρ := RatBounds.divPositive_mem h.eta (RatBounds.add_mem one h.eta) hDen
  have hratio₁ := RatBounds.divPositive_mem (he 0) (he 1) h₁
  have hratio₂ := RatBounds.divPositive_mem (he 0) (he 2) h₂
  have hβ : c.sideBetaDen.Contains (betaDen η e) :=
    RatBounds.add_mem (RatBounds.add_mem (RatBounds.add_mem one (RatBounds.sideSquare_mem hratio₁))
      (RatBounds.sideSquare_mem hratio₂)) (RatBounds.sideSquare_mem (RatBounds.mul_mem (he 0) hρ))
  have hβ₀ : ((RatBounds.point 1).divPositive c.sideBetaDen).Contains (beta η e 0) :=
    RatBounds.divPositive_mem one hβ hBeta
  have hβ₁ : (c.sideBetaFactor 1).Contains (HlawkaSchatten.BelowExponent.Vertex.sideBetaFactor η e 1) :=
    RatBounds.divPositive_mem (RatBounds.divPositive_mem (he 0) (RatBounds.sideSquare_mem (he 1)) hs₁)
      hβ hBeta
  have hβ₂ : (c.sideBetaFactor 2).Contains (HlawkaSchatten.BelowExponent.Vertex.sideBetaFactor η e 2) :=
    RatBounds.divPositive_mem (RatBounds.divPositive_mem (he 0) (RatBounds.sideSquare_mem (he 2)) hs₂)
      hβ hBeta
  have hβh : c.sideHeavyFactor.Contains (HlawkaSchatten.BelowExponent.Vertex.sideHeavyFactor η e) :=
    RatBounds.divPositive_mem
      (RatBounds.mul_mem (he 0) (RatBounds.sideSquare_mem (RatBounds.add_mem one hρ))) hβ hBeta
  have hε : c.depth.Contains (η / (1+2*η)) := by
    have mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x/(1+2*x) ≤ y/(1+2*y) := by
      apply (div_le_div_iff₀ (by positivity) (by linarith)).2
      linarith
    have hlo : (0 : ℝ) ≤ c.η.lo := by exact_mod_cast hη₀
    simpa only [RatBounds.Contains, ParameterCell.depth, Rat.cast_div, Rat.cast_add,
      Rat.cast_mul, Rat.cast_one, Rat.cast_ofNat] using
      And.intro (mono hlo h.eta.1) (mono (hlo.trans h.eta.1) h.eta.2)
  exact (c.sideGradient roots).evaluate_sound h.eta hε he (c.radical_mem hr h) hβ₀ hβ₁ hβ₂ hβh j

end

end HlawkaSchatten.BelowExponent.Vertex
