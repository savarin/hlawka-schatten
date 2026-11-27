/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeParameterIntervals

/-! One closed SC near-cone box with witnesses for its signed Taylor factors. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

structure SideNearBox where
  cell : ParameterCell
  roots : Fin 3 → RatBounds
  exponent : RatBounds
  u : RatBounds
  v : RatBounds

structure SideNearSamples where
  baseFirst : FactorSamples
  baseSlope : FactorSamples
  firstU : FactorSamples
  firstV : FactorSamples
  secondU : FactorSamples
  secondV : FactorSamples
  slopeU : FactorSamples
  slopeV : FactorSamples
  mixed : FactorSamples

structure SideNearParameterValues where
  d₁ : RatBounds
  d₂ : RatBounds
  w₀ : RatBounds
  w₁ : RatBounds
  w₂ : RatBounds
  g₁ : RatBounds
  g₂ : RatBounds
  deriving DecidableEq, Repr

def sideNearExponent : RatBounds := ⟨19/12, 27/17⟩

theorem criticalQ_mem_sideNearExponent : sideNearExponent.Contains criticalQ := by
  change ((19/12 : ℚ) : ℝ) ≤ criticalQ ∧ criticalQ ≤ ((27/17 : ℚ) : ℝ)
  push_cast
  exact ⟨(by norm_num : (19/12 : ℝ) ≤ 1054/665).trans criticalQ_bracket.1.le,
    criticalQ_bracket.2.le.trans (by norm_num)⟩

def SideNearBox.slope (B : SideNearBox) := B.exponent.sub (RatBounds.point 1)

def SideNearBox.baseShift (B : SideNearBox) := ((RatBounds.point 4).mul B.cell.η).mul B.cell.a

def SideNearBox.base (B : SideNearBox) := (RatBounds.point 1).add B.baseShift

def SideNearBox.shift (B : SideNearBox) : RatBounds :=
  let P := RatBounds.point
  let depth := (P 2).mul B.cell.η
  let C := (P 1).add (depth.mul ((P 1).sub B.cell.b))
  let D := (P 1).add (depth.mul (B.cell.a.add B.cell.b))
  (C.mul B.u).add (D.mul B.v)

def SideNearBox.argument (B : SideNearBox) := B.shift.divPositive B.base

def SideNearBox.scaledBase (B : SideNearBox) : RatBounds := ⟨1 / B.base.hi, 1⟩

def SideNearBox.dyadicValues (B : SideNearBox) := axisCoefficientIntervals B.cell B.roots 0

def SideNearBox.parameterValues (B : SideNearBox) : SideNearParameterValues :=
  let params := B.dyadicValues
  let gradient := B.cell.sideGradient B.roots
  ⟨(params.d.get 1).value.toSideRat, (params.d.get 2).value.toSideRat,
    (params.weight.get 0).value.toSideRat, (params.weight.get 1).value.toSideRat,
    (params.weight.get 2).value.toSideRat, gradient.evaluate 1, gradient.evaluate 2⟩

def SideNearBox.inputFrom (B : SideNearBox) (W : SideNearSamples) (P : SideNearParameterValues) :
    SideIntervalInputs :=
  ⟨B.exponent, B.cell.a, B.cell.b, B.cell.η,
    ![P.d₁, P.d₂], ![P.w₀, P.w₁, P.w₂], ![P.g₁, P.g₂],
    firstFactorRange B.exponent B.baseShift true W.baseFirst,
    firstFactorRange B.slope B.baseShift false W.baseSlope,
    ![firstFactorRange B.slope B.u false W.firstU, firstFactorRange B.slope B.v false W.firstV],
    ![secondFactorRange B.exponent B.u W.secondU, secondFactorRange B.exponent B.v W.secondV],
    ![secondFactorRange B.slope B.u W.slopeU, secondFactorRange B.slope B.v W.slopeV],
    B.scaledBase.mul (secondFactorRange B.exponent B.argument W.mixed)⟩

def SideNearBox.input (B : SideNearBox) (W : SideNearSamples) : SideIntervalInputs :=
  B.inputFrom W B.parameterValues

structure SideNearBox.OK (B : SideNearBox) (W : SideNearSamples) : Prop where
  roots : B.cell.rootsOK B.roots = true
  gradient : B.cell.sideGradientOK = true
  value : (B.dyadicValues.d.get 1).value.ok = true ∧ (B.dyadicValues.d.get 2).value.ok = true
  weight : ∀ j, (B.dyadicValues.weight.get j).value.ok = true
  a : 0 ≤ B.cell.a.lo
  qlo : 1 ≤ B.exponent.lo
  qhi : B.exponent.hi ≤ 2
  base : 1 ≤ B.base.lo
  firstBase : firstFactorRangeOK B.exponent B.baseShift true W.baseFirst = true
  slopeBase : firstFactorRangeOK B.slope B.baseShift false W.baseSlope = true
  firstU : firstFactorRangeOK B.slope B.u false W.firstU = true
  firstV : firstFactorRangeOK B.slope B.v false W.firstV = true
  secondU : secondFactorRangeOK B.exponent B.u W.secondU = true
  secondV : secondFactorRangeOK B.exponent B.v W.secondV = true
  slopeU : secondFactorRangeOK B.slope B.u W.slopeU = true
  slopeV : secondFactorRangeOK B.slope B.v W.slopeV = true
  mixed : secondFactorRangeOK B.exponent B.argument W.mixed = true

noncomputable section

theorem SideNearBox.evaluate_sound {B : SideNearBox} {W : SideNearSamples} (h : B.OK W)
    {q a b η u v : ℝ} (hq : B.exponent.Contains q) (hp : B.cell.Contains a b η)
    (hu : B.u.Contains u) (hv : B.v.Contains v) :
    ((B.input W).evaluate.Contains (sideCoefficients q a b η u v)) ∧
      0 ≤ a ∧ 0 ≤ η ∧ -1 < u ∧ -1 < v ∧ 0 < sideY a b η u v := by
  let C := 1 + 2*η*(1-b)
  let D := 1 + 2*η*(a+b)
  let X := 4*η*a
  let Y := 1+X
  let L := C*u+D*v
  have one : (RatBounds.point 1).Contains (1 : ℝ) := by simpa using RatBounds.point_mem 1
  have two : (RatBounds.point 2).Contains (2 : ℝ) := by simpa using RatBounds.point_mem 2
  have four : (RatBounds.point 4).Contains (4 : ℝ) := by simpa using RatBounds.point_mem 4
  have hX : B.baseShift.Contains X := RatBounds.mul_mem (RatBounds.mul_mem four hp.eta) hp.first
  have hY : B.base.Contains Y := RatBounds.add_mem one hX
  have hdepth := RatBounds.mul_mem two hp.eta
  have hC := RatBounds.add_mem one (RatBounds.mul_mem hdepth (RatBounds.sub_mem one hp.second))
  have hD := RatBounds.add_mem one (RatBounds.mul_mem hdepth (RatBounds.add_mem hp.first hp.second))
  have hL : B.shift.Contains L := RatBounds.add_mem (RatBounds.mul_mem hC hu) (RatBounds.mul_mem hD hv)
  have hbase : (1 : ℝ) ≤ B.base.lo := by exact_mod_cast h.base
  have hY₁ : 1 ≤ Y := hbase.trans hY.1
  have ht : B.argument.Contains (L/Y) :=
    RatBounds.divPositive_mem hL hY (zero_lt_one.trans_le h.base)
  have hq₁ : 1 ≤ q := (show (1 : ℝ) ≤ B.exponent.lo by exact_mod_cast h.qlo).trans hq.1
  have hq₂ : q ≤ 2 := hq.2.trans (by exact_mod_cast h.qhi)
  have hr : B.slope.Contains (q-1) := RatBounds.sub_mem hq one
  have hr₁ : q-1 ≤ 1 := by linarith only [hq₂]
  have hr₂ : q-1 ≤ 2 := hr₁.trans (by norm_num)
  have hexp : B.scaledBase.Contains (Y ^ (q-2)) := by
    constructor
    · change ((1 / B.base.hi : ℚ) : ℝ) ≤ _
      push_cast
      have hneg : -1 ≤ q-2 := by linarith only [hq₁]
      exact (one_div_le_one_div_of_le (zero_lt_one.trans_le hY₁) hY.2).trans
        (by simpa only [Real.rpow_neg_one, one_div] using
          Real.rpow_le_rpow_of_exponent_le hY₁ hneg)
    · change Y ^ (q-2) ≤ ((1 : ℚ) : ℝ)
      simpa only [Rat.cast_one, Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le hY₁ (sub_nonpos.mpr hq₂)
  have hdw := ParameterCell.coefficientValues_mem hp hp h.roots
  have hd₁ := DyadicBounds.contains_toSideRat (hdw.1 1) h.value.1
  have hd₂ := DyadicBounds.contains_toSideRat (hdw.1 2) h.value.2
  have hw j : ((B.input W).weight j).Contains (parameterWeight a b η j) := by
    fin_cases j
    · exact DyadicBounds.contains_toSideRat (hdw.2.1 0) (h.weight 0)
    · exact DyadicBounds.contains_toSideRat (hdw.2.1 1) (h.weight 1)
    · exact DyadicBounds.contains_toSideRat (hdw.2.1 2) (h.weight 2)
  have hg j := ParameterCell.sideGradient_sound h.roots h.gradient hp j
  have hF := firstFactorRange_sound h.firstBase hq hX hq₁
  have hG := firstFactorRange_sound h.slopeBase hr hX hr₁
  have hn₁ := firstFactorRange_sound h.firstU hr hu hr₁
  have hn₂ := firstFactorRange_sound h.firstV hr hv hr₁
  have hm₁ := secondFactorRange_sound h.secondU hq hu hq₂
  have hm₂ := secondFactorRange_sound h.secondV hq hv hq₂
  have hmr₁ := secondFactorRange_sound h.slopeU hr hu hr₂
  have hmr₂ := secondFactorRange_sound h.slopeV hr hv hr₂
  have hT := RatBounds.mul_mem hexp (secondFactorRange_sound h.mixed hq ht hq₂)
  have hdom {O T : RatBounds} {x : ℝ} {S : FactorSamples}
      (hcheck : secondFactorRangeOK O T S = true) (hx : T.Contains x) : -1 < x := by
    simp only [secondFactorRangeOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hcheck
    exact (show (-1 : ℝ) < (T.lo : ℝ) by exact_mod_cast hcheck.1).trans_le hx.1
  have ht₀ := hdom h.mixed ht
  have hY₀ := zero_lt_one.trans_le hY₁
  have hYplus : 0 < Y+L := by
    have hh := (lt_div_iff₀ hY₀).1 ht₀
    linarith only [hh]
  have hη : 0 ≤ B.cell.η.lo := by
    have hz := h.roots
    simp only [ParameterCell.rootsOK, Bool.and_eq_true, decide_eq_true_eq] at hz
    exact hz.1
  have hη₀ := (show (0 : ℝ) ≤ B.cell.η.lo by exact_mod_cast hη).trans hp.eta.1
  refine ⟨(B.input W).evaluate_sound hq hp.first hp.second hp.eta hη₀ hd₁ hd₂ hw (hg 1) (hg 2)
    hF hG hn₁ hn₂ hm₁ hm₂ hmr₁ hmr₂ hT, ?_, hη₀, hdom h.secondU hu, hdom h.secondV hv, ?_⟩
  · exact (show (0 : ℝ) ≤ B.cell.a.lo by exact_mod_cast h.a).trans hp.first.1
  · simpa only [sideY, Y, X, L, C, D, add_assoc] using hYplus

theorem SideNearBox.gap_nonneg_det {B : SideNearBox} {W : SideNearSamples} (h : B.OK W)
    {q a b η u v : ℝ} {s t : Bool} (hq : B.exponent.Contains q) (hp : B.cell.Contains a b η)
    (hu : B.u.Contains u) (hv : B.v.Contains v) (hs : HasSideSign s u) (ht : HasSideSign t v)
    (hdet : ((B.input W).evaluate.lower s t).detOK B.cell.a.hi = true) :
    0 ≤ parameterGap q (sideRow u v) a b η := by
  obtain ⟨hbox, ha, hη, hu₀, hv₀, hY⟩ := B.evaluate_sound h hq hp hu hv
  exact side_gap_nonneg_of_interval_det ha hp.first.2 hη hu₀ hv₀ hY hs ht hbox hdet

end

end HlawkaSchatten.BelowExponent.Vertex
