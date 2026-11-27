/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeRectangle
public import HlawkaSchatten.BelowExponent.Vertex.SideConeGrid

/-! Reflect a signed near rectangle and combine exact row certificates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def sideAxisSign (I : RatBounds) : Bool := decide (0 ≤ I.lo)

def sideAxisSignOK (I : RatBounds) : Bool := decide (0 ≤ I.lo ∨ I.hi ≤ 0)

def SideNearBox.signsOK (B : SideNearBox) : Bool := sideAxisSignOK B.u && sideAxisSignOK B.v

def SideNearBox.signBounds (B : SideNearBox) (W : SideNearSamples) : SideLowerCoefficients :=
  (B.input W).evaluate.lower (sideAxisSign B.u) (sideAxisSign B.v)

def SideNearBox.quadraticOK (B : SideNearBox) (W : SideNearSamples) : Bool :=
  let I := B.signBounds W
  I.detOK B.cell.a.hi || I.rectangleOK B.cell.a B.u B.v

def SideNearBox.parameterOK (B : SideNearBox) : Bool :=
  B.cell.rootsOK B.roots && B.cell.sideGradientOK && (B.dyadicValues.d.get 1).value.ok &&
    (B.dyadicValues.d.get 2).value.ok &&
    ((List.finRange 3).all fun j => (B.dyadicValues.weight.get j).value.ok) &&
    decide (0 ≤ B.cell.a.lo ∧ 1 ≤ B.exponent.lo ∧ B.exponent.hi ≤ 2 ∧ 1 ≤ B.base.lo)

def SideNearBox.multipliersOK (B : SideNearBox) (W : SideNearSamples) : Bool :=
  firstFactorRangeOK B.exponent B.baseShift true W.baseFirst &&
  firstFactorRangeOK B.slope B.baseShift false W.baseSlope &&
  firstFactorRangeOK B.slope B.u false W.firstU && firstFactorRangeOK B.slope B.v false W.firstV &&
  secondFactorRangeOK B.exponent B.u W.secondU && secondFactorRangeOK B.exponent B.v W.secondV &&
  secondFactorRangeOK B.slope B.u W.slopeU && secondFactorRangeOK B.slope B.v W.slopeV &&
  secondFactorRangeOK B.exponent B.argument W.mixed

theorem SideNearBox.guards_sound {B : SideNearBox} {W : SideNearSamples}
    (hp : B.parameterOK = true) (hm : B.multipliersOK W = true) : B.OK W := by
  simp only [SideNearBox.parameterOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc] at hp
  simp only [SideNearBox.multipliersOK, Bool.and_eq_true, and_assoc] at hm
  obtain ⟨hr, hg, h₁, h₂, hw, ha, hl, hh, hb⟩ := hp
  obtain ⟨hm₁, hm₂, hm₃, hm₄, hm₅, hm₆, hm₇, hm₈, hm₉⟩ := hm
  exact ⟨hr, hg, ⟨h₁,h₂⟩, fun j => hw j (by simp), ha, hl, hh, hb,
    hm₁, hm₂, hm₃, hm₄, hm₅, hm₆, hm₇, hm₈, hm₉⟩

theorem sideAxisSign_sound {I : RatBounds} {x : ℝ} (h : sideAxisSignOK I = true)
    (hx : I.Contains x) : HasSideSign (sideAxisSign I) x := by
  have hh := of_decide_eq_true h
  by_cases hlo : 0 ≤ I.lo
  · change HasSideSign (decide (0 ≤ I.lo)) x
    rw [decide_eq_true hlo]
    exact (show (0 : ℝ) ≤ (I.lo : ℝ) by exact_mod_cast hlo).trans hx.1
  · change HasSideSign (decide (0 ≤ I.lo)) x
    rw [decide_eq_false hlo]
    exact hx.2.trans (by exact_mod_cast hh.resolve_left hlo)

theorem SideNearBox.quadraticOK_sound {B : SideNearBox} {W : SideNearSamples}
    (hok : B.OK W) (hsgn : B.signsOK = true) (hcheck : B.quadraticOK W = true)
    {q a b η u v : ℝ} (hq : B.exponent.Contains q) (hp : B.cell.Contains a b η)
    (hu : B.u.Contains u) (hv : B.v.Contains v) : 0 ≤ parameterGap q (sideRow u v) a b η := by
  have hs := Bool.and_eq_true_iff.mp hsgn
  have hsu := sideAxisSign_sound hs.1 hu
  have hsv := sideAxisSign_sound hs.2 hv
  rcases Bool.or_eq_true_iff.mp hcheck with hd | hr
  · exact B.gap_nonneg_det hok hq hp hu hv hsu hsv hd
  · exact B.gap_nonneg_rectangle hok hq hp hu hv hsu hsv hr

def SideConeOn (c : ParameterCell) (U V : RatBounds) : Prop :=
  ∀ ⦃a b η u v : ℝ⦄, c.Contains a b η → U.Contains u → V.Contains v →
    0 ≤ parameterGap criticalQ (sideRow u v) a b η

theorem SideNearBox.certified {B : SideNearBox} {W : SideNearSamples}
    (hok : B.OK W) (he : B.exponent = sideNearExponent) (hsgn : B.signsOK = true)
    (hcheck : B.quadraticOK W = true) : SideConeOn B.cell B.u B.v := by
  have hq : B.exponent.Contains criticalQ := by rw [he]; exact criticalQ_mem_sideNearExponent
  intro a b η u v hp hu hv
  exact B.quadraticOK_sound hok hsgn hcheck hq hp hu hv

theorem sideConeOn_of_rowGrid {c : ParameterCell}
    (h : ∀ ij ∈ sideRowGrid, SideConeOn c (sideURange ij.1) (sideVRange ij.2))
    {a b η u v : ℝ} (hp : c.Contains a b η) (hu₀ : -5/8 ≤ u) (hu₁ : u ≤ 2)
    (hv₀ : -3/4 ≤ v) (hv₁ : v ≤ 3) (hcut : -5/8 ≤ u+v) :
    0 ≤ parameterGap criticalQ (sideRow u v) a b η := by
  obtain ⟨ij, hmem, hu, hv⟩ := sideRowGrid_cover hu₀ hu₁ hv₀ hv₁ hcut
  exact h ij hmem hp hu hv

theorem SideNearBox.checked {B : SideNearBox} {W : SideNearSamples}
    (hp : B.parameterOK = true) (hm : B.multipliersOK W = true)
    (he : B.exponent = sideNearExponent) (hsgn : B.signsOK = true) (hcheck : B.quadraticOK W = true) :
    SideConeOn B.cell B.u B.v :=
  B.certified (B.guards_sound hp hm) he hsgn hcheck

end HlawkaSchatten.BelowExponent.Vertex
