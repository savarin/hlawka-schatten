/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeRows

/-! Fixed-point evaluation of the SC quadratic coefficients. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

structure SideDyadicInputs where
  exponent : DyadicBounds
  a : DyadicBounds
  b : DyadicBounds
  eta : DyadicBounds
  coefficient : Fin 2 → DyadicBounds
  weight : Fin 3 → DyadicBounds
  factor : Fin 2 → DyadicBounds
  baseFirst : DyadicBounds
  baseSlope : DyadicBounds
  firstPower : Fin 2 → DyadicBounds
  secondPower : Fin 2 → DyadicBounds
  secondSlope : Fin 2 → DyadicBounds
  scaledSecond : DyadicBounds

structure SideDyadicCoefficients where
  value : DyadicBounds
  first : DyadicBounds
  second : DyadicBounds
  diagonalFirst : DyadicBounds
  mixed : DyadicBounds
  diagonalSecond : DyadicBounds

def SideDyadicCoefficients.toRat (I : SideDyadicCoefficients) : SideCoefficientIntervals :=
  ⟨I.value.toSideRat, I.first.toSideRat, I.second.toSideRat,
    I.diagonalFirst.toSideRat, I.mixed.toSideRat, I.diagonalSecond.toSideRat⟩

def SideDyadicInputs.ofRat (I : SideIntervalInputs) : SideDyadicInputs :=
  ⟨.ofRat I.exponent, .ofRat I.a, .ofRat I.b, .ofRat I.eta,
    fun j => .ofRat (I.coefficient j), fun j => .ofRat (I.weight j), fun j => .ofRat (I.factor j),
    .ofRat I.baseFirst, .ofRat I.baseSlope, fun j => .ofRat (I.firstPower j),
    fun j => .ofRat (I.secondPower j), fun j => .ofRat (I.secondSlope j), .ofRat I.scaledSecond⟩

def SideDyadicInputs.directDiagonal (I : SideDyadicInputs) (i : Fin 2)
    (w arg base : DyadicBounds) : DyadicBounds :=
  let P := DyadicBounds.point
  let r := I.exponent.sub (P 1)
  let first := (I.coefficient i).mul (I.secondPower i)
  let second := (((P 2).mul arg).mul w).mul (I.firstPower i)
  let third := ((((P 2).mul I.a).mul (r.sub (P 1))).mul w).mul (I.secondSlope i)
  ((first.add second).add third).sub ((base.mul base).mul I.scaledSecond)

def SideDyadicInputs.centeredDiagonal (I : SideDyadicInputs) (i : Fin 2)
    (w other arg base : DyadicBounds) : DyadicBounds :=
  let P := DyadicBounds.point
  let r := I.exponent.sub (P 1)
  let signed := (((I.weight 0).add w).sub other).sub (((P 2).mul I.eta).mul base)
  let H := (I.a.mul (I.factor i)).add (arg.mul signed)
  let first := (I.coefficient i).mul ((I.secondPower i).sub (P 1))
  let second := (((P 2).mul arg).mul w).mul ((I.firstPower i).sub (P 1))
  let third := ((((P 2).mul I.a).mul (r.sub (P 1))).mul w).mul (I.secondSlope i)
  (((H.add first).add second).add third).sub ((base.mul base).mul (I.scaledSecond.sub (P 1)))

def SideDyadicInputs.evaluate (I : SideDyadicInputs) : SideDyadicCoefficients :=
  let P := DyadicBounds.point
  let r := I.exponent.sub (P 1)
  let A := (P 1).sub I.b
  let B := I.a.add I.b
  let C := (P 1).add (((P 2).mul I.eta).mul A)
  let D := (P 1).add (((P 2).mul I.eta).mul B)
  let J := ((I.weight 0).sub (I.weight 1)).sub (I.weight 2)
  let k := (I.exponent.mul r).mul (P (1/2))
  let a₄ := (P 4).mul I.eta
  let constant := (((P (-2)).mul I.exponent).mul J).sub
    ((a₄.mul I.exponent).mul I.baseFirst)
  let gradient (i : Fin 2) (w base : DyadicBounds) :=
    I.exponent.mul (((I.factor i).add (((P 2).mul r).mul w)).sub
      (((a₄.mul r).mul base).mul I.baseSlope))
  let diag (i : Fin 2) (w other arg base : DyadicBounds) :=
    k.mul ((I.directDiagonal i w arg base).intersect (I.centeredDiagonal i w other arg base))
  let mixed := k.mul (((((A.mul (I.weight 2)).mul (I.firstPower 1)).add
    ((B.mul (I.weight 1)).mul (I.firstPower 0))).sub ((C.mul D).mul I.scaledSecond)))
  ⟨constant, gradient 0 (I.weight 1) C, gradient 1 (I.weight 2) D,
    diag 0 (I.weight 1) (I.weight 2) A C, mixed, diag 1 (I.weight 2) (I.weight 1) B D⟩

def SideDyadicCoefficients.valid (I : SideDyadicCoefficients) : Bool :=
  I.value.ok && I.first.ok && I.second.ok && I.diagonalFirst.ok && I.mixed.ok && I.diagonalSecond.ok

def SideNearRowData.checkFixed (D : SideNearRowData) (c : ParameterCell) (roots : Fin 3 → RatBounds)
    (P : SideNearParameterValues) : Bool :=
  let B := D.box c roots
  let A := (SideDyadicInputs.ofRat (B.inputFrom D.samples P)).evaluate
  let I := A.toRat.lower (sideAxisSign B.u) (sideAxisSign B.v)
  B.signsOK && B.multipliersOK D.samples && A.valid &&
    (I.detOK c.a.hi || I.rectangleOK c.a B.u B.v)

noncomputable section

structure SideDyadicCoefficients.Contains (I : SideDyadicCoefficients) (c : SideCoefficients) : Prop where
  value : I.value.Contains c.value
  first : I.first.Contains c.first
  second : I.second.Contains c.second
  diagonalFirst : I.diagonalFirst.Contains c.diagonalFirst
  mixed : I.mixed.Contains c.mixed
  diagonalSecond : I.diagonalSecond.Contains c.diagonalSecond

private theorem side_dyadic_one : (DyadicBounds.point 1).Contains (1 : ℝ) := by
  simpa only [Rat.cast_one] using DyadicBounds.point_mem 1

private theorem side_dyadic_two : (DyadicBounds.point 2).Contains (2 : ℝ) := by
  simpa only [Rat.cast_ofNat] using DyadicBounds.point_mem 2

private theorem side_dyadic_four : (DyadicBounds.point 4).Contains (4 : ℝ) := by
  simpa only [Rat.cast_ofNat] using DyadicBounds.point_mem 4

private theorem side_dyadic_neg_two : (DyadicBounds.point (-2)).Contains (-2 : ℝ) := by
  simpa only [Rat.cast_neg, Rat.cast_ofNat] using DyadicBounds.point_mem (-2)

theorem SideDyadicInputs.evaluate_sound (I : SideDyadicInputs) {q a b η u v : ℝ}
    (hQ : I.exponent.Contains q) (ha : I.a.Contains a) (hb : I.b.Contains b) (he : I.eta.Contains η)
    (hη : 0 ≤ η) :
    let e := parameterDirection a b
    let R := radical (η / (1 + 2 * η)) e
    let d := parameterD a b η
    let W := rowWeight η R d
    let r := q-1
    let X := 4*η*a
    let Y := 1+X
    let t := ((1+2*η*(1-b))*u + (1+2*η*(a+b))*v) / Y
    (I.coefficient 0).Contains (d 1) →
    (I.coefficient 1).Contains (d 2) →
    (∀ j, (I.weight j).Contains (W j)) →
    (I.factor 0).Contains (sideGradientFactor η e R 1) →
    (I.factor 1).Contains (sideGradientFactor η e R 2) →
    I.baseFirst.Contains (sideFirstFactor q X) →
    I.baseSlope.Contains (sideFirstFactor r X) →
    (I.firstPower 0).Contains (sideFirstFactor r u) →
    (I.firstPower 1).Contains (sideFirstFactor r v) →
    (I.secondPower 0).Contains (sideSecondFactor q u) →
    (I.secondPower 1).Contains (sideSecondFactor q v) →
    (I.secondSlope 0).Contains (sideSecondFactor r u) →
    (I.secondSlope 1).Contains (sideSecondFactor r v) →
    I.scaledSecond.Contains (Y ^ (q-2) * sideSecondFactor q t) →
    I.evaluate.Contains (sideCoefficients q a b η u v) := by
  intro e R d W r X Y t hd₁ hd₂ hw hg₁ hg₂ hF hG hn₁ hn₂ hm₁ hm₂ hmr₁ hmr₂ hT
  let A := 1-b
  let B := a+b
  let C := 1+2*η*A
  let D := 1+2*η*B
  have hr := DyadicBounds.Contains.sub hQ side_dyadic_one
  have hr₁ := DyadicBounds.Contains.sub hr side_dyadic_one
  have hA := DyadicBounds.Contains.sub side_dyadic_one hb
  have hB := DyadicBounds.Contains.add ha hb
  have h2e := DyadicBounds.Contains.mul side_dyadic_two he
  have hC := DyadicBounds.Contains.add side_dyadic_one (DyadicBounds.Contains.mul h2e hA)
  have hD := DyadicBounds.Contains.add side_dyadic_one (DyadicBounds.Contains.mul h2e hB)
  have hJ := DyadicBounds.Contains.sub (DyadicBounds.Contains.sub (hw 0) (hw 1)) (hw 2)
  have hK := DyadicBounds.Contains.mul (DyadicBounds.Contains.mul hQ hr) (DyadicBounds.point_mem (1 / 2))
  have hK' : ((I.exponent.mul (I.exponent.sub (DyadicBounds.point 1))).mul
      (DyadicBounds.point (1/2))).Contains (q * r / 2) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, mul_one_div] using hK
  have h4e := DyadicBounds.Contains.mul side_dyadic_four he
  have hc := DyadicBounds.Contains.sub (DyadicBounds.Contains.mul (DyadicBounds.Contains.mul side_dyadic_neg_two hQ) hJ)
    (DyadicBounds.Contains.mul (DyadicBounds.Contains.mul h4e hQ) hF)
  have gradient {i : Fin 2} {w t g : ℝ} {W T : DyadicBounds}
      (hw : W.Contains w) (ht : T.Contains t) (hg : (I.factor i).Contains g) :=
    DyadicBounds.Contains.mul hQ
      (DyadicBounds.Contains.sub (DyadicBounds.Contains.add hg (DyadicBounds.Contains.mul (DyadicBounds.Contains.mul side_dyadic_two hr) hw))
        (DyadicBounds.Contains.mul (DyadicBounds.Contains.mul (DyadicBounds.Contains.mul h4e hr) ht) hG))
  let F := Y^(q-2)*sideSecondFactor q t
  have hf : I.scaledSecond.Contains F := hT
  have diagonal {i : Fin 2} {d w o s z n m mr g : ℝ} {Wb O S T : DyadicBounds}
      (hd : (I.coefficient i).Contains d) (hwj : Wb.Contains w) (hs : S.Contains s) (ht : T.Contains z)
      (hn : (I.firstPower i).Contains n) (hm : (I.secondPower i).Contains m)
      (hmr : (I.secondSlope i).Contains mr) (ho : O.Contains o) (hg : (I.factor i).Contains g)
      (hlinear : d - s * (W 0 - w - o) - z = a*g) (hbase : z = 1+2*η*s) :
      ((((I.exponent.mul (I.exponent.sub (DyadicBounds.point 1))).mul (DyadicBounds.point (1/2))).mul
        ((I.directDiagonal i Wb S T).intersect (I.centeredDiagonal i Wb O S T)))).Contains
        (q*r/2*(d*m+2*s*w*n+2*a*(r-1)*w*mr-z*z*F)) := by
    have hslope := DyadicBounds.Contains.mul (DyadicBounds.Contains.mul side_dyadic_two hs) hwj
    have hthird := DyadicBounds.Contains.mul
      (DyadicBounds.Contains.mul (DyadicBounds.Contains.mul (DyadicBounds.Contains.mul side_dyadic_two ha) hr₁) hwj) hmr
    have hsquare := DyadicBounds.Contains.mul ht ht
    have direct := DyadicBounds.Contains.sub (DyadicBounds.Contains.add
      (DyadicBounds.Contains.add (DyadicBounds.Contains.mul hd hm) (DyadicBounds.Contains.mul hslope hn)) hthird)
      (DyadicBounds.Contains.mul hsquare hf)
    have hSigned := DyadicBounds.Contains.sub (DyadicBounds.Contains.sub (DyadicBounds.Contains.add (hw 0) hwj) ho)
      (DyadicBounds.Contains.mul h2e ht)
    have hH := DyadicBounds.Contains.add (DyadicBounds.Contains.mul ha hg) (DyadicBounds.Contains.mul hs hSigned)
    have centered := DyadicBounds.Contains.sub (DyadicBounds.Contains.add
      (DyadicBounds.Contains.add (DyadicBounds.Contains.add hH (DyadicBounds.Contains.mul hd (DyadicBounds.Contains.sub hm side_dyadic_one)))
        (DyadicBounds.Contains.mul hslope (DyadicBounds.Contains.sub hn side_dyadic_one))) hthird)
      (DyadicBounds.Contains.mul hsquare (DyadicBounds.Contains.sub hf side_dyadic_one))
    have heq : a*g+s*(W 0+w-o-2*η*z)+d*(m-1)+2*s*w*(n-1)+2*a*(r-1)*w*mr-z*z*(F-1) =
        d*m+2*s*w*n+2*a*(r-1)*w*mr-z*z*F := by
      linear_combination -hlinear + z*hbase
    rw [heq] at centered
    exact DyadicBounds.Contains.mul hK' (DyadicBounds.Contains.intersect direct centered)
  have hMix := DyadicBounds.Contains.mul hK'
    (DyadicBounds.Contains.sub (DyadicBounds.Contains.add
      (DyadicBounds.Contains.mul (DyadicBounds.Contains.mul hA (hw 2)) hn₂)
      (DyadicBounds.Contains.mul (DyadicBounds.Contains.mul hB (hw 1)) hn₁))
      (DyadicBounds.Contains.mul (DyadicBounds.Contains.mul hC hD) hT))
  have lin₁ : d 1 - A * (W 0 - W 1 - W 2) - C = a * sideGradientFactor η e R 1 :=
    side_linear_factor hη (by decide : (1 : Fin 3) ≠ 0)
  have lin₂ : d 2 - B * (W 0 - W 2 - W 1) - D = a * sideGradientFactor η e R 2 := by
    have this := side_linear_factor (a := a) (b := b) hη (by decide : (2 : Fin 3) ≠ 0)
    change d 2 - (1-(1-a-b)) * (W 0-W 1-W 2) - (1+2*η*(1-(1-a-b))) =
      a*sideGradientFactor η e R 2 at this
    dsimp only [B,D]
    linear_combination this
  constructor
  · exact hc
  · exact gradient (hw 1) hC hg₁
  · exact gradient (hw 2) hD hg₂
  · simpa only [SideDyadicInputs.evaluate, sideCoefficients, pow_two] using
      diagonal hd₁ (hw 1) hA hC hn₁ hm₁ hmr₁ (hw 2) hg₁ lin₁ rfl
  · exact hMix
  · simpa only [SideDyadicInputs.evaluate, sideCoefficients, pow_two] using
      diagonal hd₂ (hw 2) hB hD hn₂ hm₂ hmr₂ (hw 1) hg₂ lin₂ rfl

theorem SideNearBox.evaluate_fixed_sound {B : SideNearBox} {W : SideNearSamples} (h : B.OK W)
    (hvalid : (SideDyadicInputs.ofRat (B.input W)).evaluate.valid = true)
    {q a b η u v : ℝ} (hq : B.exponent.Contains q) (hp : B.cell.Contains a b η)
    (hu : B.u.Contains u) (hv : B.v.Contains v) :
    ((SideDyadicInputs.ofRat (B.input W)).evaluate.toRat.Contains (sideCoefficients q a b η u v)) ∧
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
  let I := SideDyadicInputs.ofRat (B.input W)
  have hfixed := I.evaluate_sound (DyadicBounds.ofRat_mem hq) (DyadicBounds.ofRat_mem hp.first)
    (DyadicBounds.ofRat_mem hp.second) (DyadicBounds.ofRat_mem hp.eta) hη₀
    (DyadicBounds.ofRat_mem hd₁) (DyadicBounds.ofRat_mem hd₂) (fun j => DyadicBounds.ofRat_mem (hw j))
    (DyadicBounds.ofRat_mem (hg 1)) (DyadicBounds.ofRat_mem (hg 2))
    (DyadicBounds.ofRat_mem hF) (DyadicBounds.ofRat_mem hG)
    (DyadicBounds.ofRat_mem hn₁) (DyadicBounds.ofRat_mem hn₂) (DyadicBounds.ofRat_mem hm₁)
    (DyadicBounds.ofRat_mem hm₂) (DyadicBounds.ofRat_mem hmr₁) (DyadicBounds.ofRat_mem hmr₂)
    (DyadicBounds.ofRat_mem hT)
  have hf : I.evaluate.toRat.Contains (sideCoefficients q a b η u v) := by
    change I.evaluate.valid = true at hvalid
    simp only [SideDyadicCoefficients.valid, Bool.and_eq_true, and_assoc] at hvalid
    exact ⟨DyadicBounds.contains_toSideRat hfixed.value hvalid.1,
      DyadicBounds.contains_toSideRat hfixed.first hvalid.2.1,
      DyadicBounds.contains_toSideRat hfixed.second hvalid.2.2.1,
      DyadicBounds.contains_toSideRat hfixed.diagonalFirst hvalid.2.2.2.1,
      DyadicBounds.contains_toSideRat hfixed.mixed hvalid.2.2.2.2.1,
      DyadicBounds.contains_toSideRat hfixed.diagonalSecond hvalid.2.2.2.2.2⟩
  refine ⟨hf, ?_, hη₀, hdom h.secondU hu, hdom h.secondV hv, ?_⟩
  · exact (show (0 : ℝ) ≤ B.cell.a.lo by exact_mod_cast h.a).trans hp.first.1
  · simpa only [sideY, Y, X, L, C, D, add_assoc] using hYplus


theorem SideNearRowData.checkFixed_sound {D : SideNearRowData} {c : ParameterCell} {roots : Fin 3 → RatBounds}
    {P : SideNearParameterValues} (hp : sideNearParameterGuard c roots = true)
    (hP : P = sideNearCanonicalValues c roots) (h : D.checkFixed c roots P = true) :
    SideConeOn c (sideURange D.row.1) (sideVRange D.row.2) := by
  subst P
  let B := D.box c roots
  simp only [SideNearRowData.checkFixed, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hsgn, hm, hvd, htest⟩ := h
  have hok : B.OK D.samples := SideNearBox.guards_sound hp hm
  intro a b η u v hc hu hv
  obtain ⟨hI, ha, he, hu₀, hv₀, hY⟩ := B.evaluate_fixed_sound
    hok hvd criticalQ_mem_sideNearExponent hc hu hv
  have hs := Bool.and_eq_true_iff.mp hsgn
  have hsu := sideAxisSign_sound hs.1 hu
  have hsv := sideAxisSign_sound hs.2 hv
  rcases Bool.or_eq_true_iff.mp htest with hd | hr
  · exact side_gap_nonneg_of_interval_det ha hc.first.2 he hu₀ hv₀ hY hsu hsv hI hd
  · rw [side_gap_eq_quadratic ha he hu₀ hv₀ hY]
    exact (SideLowerCoefficients.rectangleOK_sound hr hc.first hu hv).trans
      (SideCoefficientIntervals.lower_le hI ha hsu hsv)

end

end HlawkaSchatten.BelowExponent.Vertex
