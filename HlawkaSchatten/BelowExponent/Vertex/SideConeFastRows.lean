/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeFixed

/-! Share the fixed-point parameter terms and the one-dimensional row factors across SC boxes. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

structure SideFastAxisSamples where
  first : FactorSamples
  second : FactorSamples
  slope : FactorSamples

structure SideFastAxisIntervals where
  first : DyadicBounds
  second : DyadicBounds
  slope : DyadicBounds
  deriving DecidableEq

def SideFastAxisSamples.intervals (S : SideFastAxisSamples) (X : RatBounds) : SideFastAxisIntervals :=
  let q := sideNearExponent
  let r := q.sub (RatBounds.point 1)
  ⟨.ofRat (firstFactorRange r X false S.first), .ofRat (secondFactorRange q X S.second),
    .ofRat (secondFactorRange r X S.slope)⟩

def SideFastAxisSamples.check (S : SideFastAxisSamples) (X : RatBounds) : Bool :=
  let q := sideNearExponent
  let r := q.sub (RatBounds.point 1)
  firstFactorRangeOK r X false S.first && secondFactorRangeOK q X S.second && secondFactorRangeOK r X S.slope

structure SideFastAxis where
  samples : SideFastAxisSamples
  bounds : SideFastAxisIntervals

def SideFastAxis.check (S : SideFastAxis) (X : RatBounds) : Bool :=
  S.samples.check X && decide (S.bounds = S.samples.intervals X)

structure SideFastDiagonalTerms where
  d : DyadicBounds
  first : DyadicBounds
  slope : DyadicBounds
  baseSquared : DyadicBounds
  center : DyadicBounds
  deriving DecidableEq

def SideFastDiagonalTerms.evaluate (T : SideFastDiagonalTerms) (R : SideFastAxisIntervals)
    (F : DyadicBounds) : DyadicBounds :=
  let one := DyadicBounds.point 1
  let slope := T.slope.mul R.slope
  let direct := (((T.d.mul R.second).add (T.first.mul R.first)).add slope).sub (T.baseSquared.mul F)
  let centered := (((T.center.add (T.d.mul (R.second.sub one))).add
    (T.first.mul (R.first.sub one))).add slope).sub (T.baseSquared.mul (F.sub one))
  direct.intersect centered

structure SideFastParameterTerms where
  value : DyadicBounds
  first : DyadicBounds
  second : DyadicBounds
  scale : DyadicBounds
  diagU : SideFastDiagonalTerms
  diagV : SideFastDiagonalTerms
  mixedU : DyadicBounds
  mixedV : DyadicBounds
  mixedBase : DyadicBounds
  deriving DecidableEq

def SideDyadicInputs.parameterTerms (I : SideDyadicInputs) : SideFastParameterTerms :=
  let P := DyadicBounds.point
  let r := I.exponent.sub (P 1)
  let A := (P 1).sub I.b
  let B := I.a.add I.b
  let twoEta := (P 2).mul I.eta
  let C := (P 1).add (twoEta.mul A)
  let D := (P 1).add (twoEta.mul B)
  let J := ((I.weight 0).sub (I.weight 1)).sub (I.weight 2)
  let k := (I.exponent.mul r).mul (P (1/2))
  let a₄ := (P 4).mul I.eta
  let value := (((P (-2)).mul I.exponent).mul J).sub ((a₄.mul I.exponent).mul I.baseFirst)
  let gradient (i : Fin 2) (w base : DyadicBounds) :=
    I.exponent.mul (((I.factor i).add (((P 2).mul r).mul w)).sub
      (((a₄.mul r).mul base).mul I.baseSlope))
  let diag (i : Fin 2) (w other arg base : DyadicBounds) : SideFastDiagonalTerms :=
    let signed := (((I.weight 0).add w).sub other).sub (twoEta.mul base)
    ⟨I.coefficient i, ((P 2).mul arg).mul w, (((P 2).mul I.a).mul (r.sub (P 1))).mul w,
      base.mul base, (I.a.mul (I.factor i)).add (arg.mul signed)⟩
  ⟨value, gradient 0 (I.weight 1) C, gradient 1 (I.weight 2) D, k,
    diag 0 (I.weight 1) (I.weight 2) A C, diag 1 (I.weight 2) (I.weight 1) B D,
    B.mul (I.weight 1), A.mul (I.weight 2), C.mul D⟩

def SideFastParameterTerms.evaluate (P : SideFastParameterTerms) (U V : SideFastAxisIntervals)
    (F : DyadicBounds) : SideDyadicCoefficients :=
  ⟨P.value, P.first, P.second, P.scale.mul (P.diagU.evaluate U F),
    P.scale.mul (((P.mixedV.mul V.first).add (P.mixedU.mul U.first)).sub (P.mixedBase.mul F)),
    P.scale.mul (P.diagV.evaluate V F)⟩

theorem SideDyadicInputs.evaluate_staged (I : SideDyadicInputs) :
    I.parameterTerms.evaluate ⟨I.firstPower 0,I.secondPower 0,I.secondSlope 0⟩
      ⟨I.firstPower 1,I.secondPower 1,I.secondSlope 1⟩ I.scaledSecond = I.evaluate := rfl

structure SideFastParameter where
  cell : ParameterCell
  roots : Fin 3 → RatBounds
  first : FactorSamples
  slope : FactorSamples
  terms : SideFastParameterTerms

def SideFastParameter.box (P : SideFastParameter) (U V : RatBounds) : SideNearBox :=
  ⟨P.cell, P.roots, sideNearExponent, U, V⟩

def SideFastParameter.pack (P : SideFastParameter) (U V : SideFastAxisSamples)
    (mixed : FactorSamples) : SideNearSamples :=
  ⟨P.first, P.slope, U.first, V.first, U.second, V.second, U.slope, V.slope, mixed⟩

def SideFastParameter.canonical (P : SideFastParameter) : SideFastParameterTerms :=
  let B := P.box (RatBounds.point 0) (RatBounds.point 0)
  let zero : FactorSamples := ⟨RatBounds.point 1, RatBounds.point 1⟩
  let z : SideFastAxisSamples := ⟨zero,zero,zero⟩
  (SideDyadicInputs.ofRat (B.input (P.pack z z zero))).parameterTerms

def SideFastParameter.check (P : SideFastParameter) : Bool :=
  let B := P.box (RatBounds.point 0) (RatBounds.point 0)
  B.parameterOK && firstFactorRangeOK B.exponent B.baseShift true P.first &&
    firstFactorRangeOK B.slope B.baseShift false P.slope && decide (P.terms = P.canonical)

def SideFastParameter.mixedInterval (P : SideFastParameter) (U V : RatBounds)
    (mixed : FactorSamples) : DyadicBounds :=
  let B := P.box U V
  .ofRat (B.scaledBase.mul (secondFactorRange B.exponent B.argument mixed))

def SideFastParameter.leafCheck (P : SideFastParameter) (U V : RatBounds)
    (U' V' : SideFastAxis) (mixed : FactorSamples) : Bool :=
  let B := P.box U V
  let A := P.terms.evaluate U'.bounds V'.bounds (P.mixedInterval U V mixed)
  let I := A.toRat.lower (sideAxisSign U) (sideAxisSign V)
  B.signsOK && secondFactorRangeOK B.exponent B.argument mixed && A.valid &&
    (I.detOK P.cell.a.hi || I.rectangleOK P.cell.a U V)

namespace PackedSideTrial

theorem parameterTerms_congr {I J : SideDyadicInputs}
    (hq : I.exponent = J.exponent) (ha : I.a = J.a) (hb : I.b = J.b) (he : I.eta = J.eta)
    (hc : I.coefficient = J.coefficient) (hw : I.weight = J.weight) (hf : I.factor = J.factor)
    (hF : I.baseFirst = J.baseFirst) (hS : I.baseSlope = J.baseSlope) :
    I.parameterTerms = J.parameterTerms := by
  cases I
  cases J
  cases hq
  cases ha
  cases hb
  cases he
  cases hc
  cases hw
  cases hf
  cases hF
  cases hS
  rfl

def inputs (P : SideFastParameter) (U V : RatBounds) (S T : SideFastAxisSamples)
    (M : FactorSamples) : SideDyadicInputs :=
  .ofRat ((P.box U V).input (P.pack S T M))

section

def emptySample : FactorSamples := ⟨RatBounds.point 1, RatBounds.point 1⟩
def emptyAxis : SideFastAxisSamples := ⟨emptySample, emptySample, emptySample⟩

theorem referenceTerms (P : SideFastParameter) :
    P.canonical = (inputs P (RatBounds.point 0) (RatBounds.point 0) emptyAxis emptyAxis emptySample).parameterTerms :=
  rfl

def rowValues (c : ParameterCell) (r : Fin 3 → RatBounds) : SideNearParameterValues :=
  let params := axisCoefficientIntervals c r 0
  let gradient := c.sideGradient r
  ⟨(params.d.get 1).value.toSideRat, (params.d.get 2).value.toSideRat,
    (params.weight.get 0).value.toSideRat, (params.weight.get 1).value.toSideRat,
    (params.weight.get 2).value.toSideRat, gradient.evaluate 1, gradient.evaluate 2⟩

variable (P : SideFastParameter) (U V : RatBounds) (S T : SideFastAxisSamples) (M : FactorSamples)

theorem readExponent : (inputs P U V S T M).exponent = .ofRat sideNearExponent := rfl
theorem readA : (inputs P U V S T M).a = .ofRat P.cell.a := rfl
theorem readB : (inputs P U V S T M).b = .ofRat P.cell.b := rfl
theorem readEta : (inputs P U V S T M).eta = .ofRat P.cell.η := rfl

def coefficients (K : SideNearParameterValues) (j : Fin 2) : DyadicBounds := .ofRat (![K.d₁, K.d₂] j)
def weights (K : SideNearParameterValues) (j : Fin 3) : DyadicBounds := .ofRat (![K.w₀, K.w₁, K.w₂] j)
def factors (K : SideNearParameterValues) (j : Fin 2) : DyadicBounds := .ofRat (![K.g₁, K.g₂] j)

theorem readCoefficient : (inputs P U V S T M).coefficient = coefficients (rowValues P.cell P.roots) := rfl
theorem readWeight : (inputs P U V S T M).weight = weights (rowValues P.cell P.roots) := rfl
theorem readFactor : (inputs P U V S T M).factor = factors (rowValues P.cell P.roots) := rfl

def baseShift (c : ParameterCell) : RatBounds := ((RatBounds.point 4).mul c.η).mul c.a

theorem readFirst : (inputs P U V S T M).baseFirst =
    DyadicBounds.ofRat (firstFactorRange sideNearExponent (baseShift P.cell) true P.first) := rfl
theorem readSlope : (inputs P U V S T M).baseSlope = DyadicBounds.ofRat
    (firstFactorRange (sideNearExponent.sub (RatBounds.point 1)) (baseShift P.cell) false P.slope) := rfl

theorem twoRowsThroughFields (P : SideFastParameter) (U V X Y : RatBounds)
    (S T A B : SideFastAxisSamples) (M N : FactorSamples) :
    (inputs P U V S T M).parameterTerms = (inputs P X Y A B N).parameterTerms :=
  parameterTerms_congr (I := inputs P U V S T M) (J := inputs P X Y A B N)
    ((readExponent P U V S T M).trans (readExponent P X Y A B N).symm)
    ((readA P U V S T M).trans (readA P X Y A B N).symm)
    ((readB P U V S T M).trans (readB P X Y A B N).symm)
    ((readEta P U V S T M).trans (readEta P X Y A B N).symm)
    ((readCoefficient P U V S T M).trans (readCoefficient P X Y A B N).symm)
    ((readWeight P U V S T M).trans (readWeight P X Y A B N).symm)
    ((readFactor P U V S T M).trans (readFactor P X Y A B N).symm)
    ((readFirst P U V S T M).trans (readFirst P X Y A B N).symm)
    ((readSlope P U V S T M).trans (readSlope P X Y A B N).symm)

theorem canonicalTerms (P : SideFastParameter) (U V : RatBounds)
    (S T : SideFastAxisSamples) (M : FactorSamples) :
    P.canonical = (inputs P U V S T M).parameterTerms :=
  (referenceTerms P).trans
    (twoRowsThroughFields P (RatBounds.point 0) (RatBounds.point 0) U V emptyAxis emptyAxis S T emptySample M)

end

theorem evaluate_congr {A B : SideFastParameterTerms} {U₁ U₂ V₁ V₂ : SideFastAxisIntervals}
    {F₁ F₂ : DyadicBounds} (hAB : A = B) (hU : U₁ = U₂) (hV : V₁ = V₂) (hF : F₁ = F₂) :
    A.evaluate U₁ V₁ F₁ = B.evaluate U₂ V₂ F₂ := by
  cases hAB
  cases hU
  cases hV
  cases hF
  rfl

theorem coefficients_eq {P : SideFastParameter} {U V : RatBounds} {S T : SideFastAxis}
    (M : FactorSamples) (ht : P.terms = P.canonical)
    (hU : S.bounds = S.samples.intervals U) (hV : T.bounds = T.samples.intervals V) :
    P.terms.evaluate S.bounds T.bounds (P.mixedInterval U V M) =
      (inputs P U V S.samples T.samples M).evaluate := by
  let I := inputs P U V S.samples T.samples M
  refine Eq.trans ?_ I.evaluate_staged
  exact evaluate_congr (ht.trans (canonicalTerms P U V S.samples T.samples M))
    (hU.trans (show S.samples.intervals U = ⟨I.firstPower 0, I.secondPower 0, I.secondSlope 0⟩ from rfl))
    (hV.trans (show T.samples.intervals V = ⟨I.firstPower 1, I.secondPower 1, I.secondSlope 1⟩ from rfl))
    (show P.mixedInterval U V M = I.scaledSecond from rfl)

def accepts (A : SideDyadicCoefficients) (c : ParameterCell) (U V : RatBounds) : Bool :=
  let L := A.toRat.lower (sideAxisSign U) (sideAxisSign V)
  L.detOK c.a.hi || L.rectangleOK c.a U V

theorem transfer {A D : SideDyadicCoefficients} (c : ParameterCell) (U V : RatBounds)
    (same : A = D) (hv : A.valid = true) (hm : accepts A c U V = true) :
    D.valid = true ∧ accepts D c U V = true := by
  cases same
  exact ⟨hv, hm⟩

theorem cone_of_checks {B : SideNearBox} {W : SideNearSamples}
    (ok : B.OK W) (hq : B.exponent.Contains criticalQ) (sgn : B.signsOK = true)
    (valid : (SideDyadicInputs.ofRat (B.input W)).evaluate.valid = true)
    (bound : accepts (SideDyadicInputs.ofRat (B.input W)).evaluate B.cell B.u B.v = true) :
    SideConeOn B.cell B.u B.v := by
  intro a b η u v hc hu hv
  obtain ⟨hI, ha, he, hu₀, hv₀, hY⟩ := B.evaluate_fixed_sound ok valid hq hc hu hv
  have hs := Bool.and_eq_true_iff.mp sgn
  have hsu := sideAxisSign_sound hs.1 hu
  have hsv := sideAxisSign_sound hs.2 hv
  rcases Bool.or_eq_true_iff.mp bound with hd | hr
  · exact side_gap_nonneg_of_interval_det ha hc.first.2 he hu₀ hv₀ hY hsu hsv hI hd
  · rw [side_gap_eq_quadratic ha he hu₀ hv₀ hY]
    exact (SideLowerCoefficients.rectangleOK_sound hr hc.first hu hv).trans
      (SideCoefficientIntervals.lower_le hI ha hsu hsv)

theorem four_checks {a b c d : Bool} (h : (a && b && c && d) = true) :
    a = true ∧ b = true ∧ c = true ∧ d = true := by
  simpa only [Bool.and_eq_true, and_assoc] using h

theorem leaf {P : SideFastParameter} {U V : RatBounds} {S T : SideFastAxis}
    {M : FactorSamples} (hP : P.check = true) (hU : S.check U = true)
    (hV : T.check V = true) (h : P.leafCheck U V S T M = true) : SideConeOn P.cell U V := by
  obtain ⟨hp, base, slope, terms⟩ := four_checks hP
  obtain ⟨u₁, u₂, us, utable⟩ := four_checks hU
  obtain ⟨v₁, v₂, vs, vtable⟩ := four_checks hV
  obtain ⟨sgn, mix, valid, bound⟩ := four_checks h
  let B := P.box U V
  let W := P.pack S.samples T.samples M
  have ok : B.OK W := SideNearBox.guards_sound hp (by
    simp only [SideNearBox.multipliersOK, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨base, slope⟩, u₁⟩, v₁⟩, u₂⟩, v₂⟩, us⟩, vs⟩, mix⟩)
  have same := coefficients_eq M (of_decide_eq_true terms)
    (of_decide_eq_true utable) (of_decide_eq_true vtable)
  obtain ⟨hv, hm⟩ := transfer P.cell U V same valid bound
  exact cone_of_checks (B := B) (W := W) ok criticalQ_mem_sideNearExponent sgn hv hm

end PackedSideTrial

theorem SideFastParameter.leafCheck_sound {P : SideFastParameter} {U V : RatBounds}
    {U' V' : SideFastAxis} {M : FactorSamples} (hP : P.check = true) (hU : U'.check U = true)
    (hV : V'.check V = true) (h : P.leafCheck U V U' V' M = true) : SideConeOn P.cell U V :=
  PackedSideTrial.leaf hP hU hV h

end HlawkaSchatten.BelowExponent.Vertex
