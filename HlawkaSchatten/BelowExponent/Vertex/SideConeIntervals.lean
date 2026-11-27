/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeBounds
public import HlawkaSchatten.BelowExponent.Vertex.SideConePowerData

/-! Exact interval evaluation of the six normalized SC coefficients. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

structure SideIntervalInputs where
  exponent : RatBounds
  a : RatBounds
  b : RatBounds
  eta : RatBounds
  coefficient : Fin 2 → RatBounds
  weight : Fin 3 → RatBounds
  factor : Fin 2 → RatBounds
  baseFirst : RatBounds
  baseSlope : RatBounds
  firstPower : Fin 2 → RatBounds
  secondPower : Fin 2 → RatBounds
  secondSlope : Fin 2 → RatBounds
  scaledSecond : RatBounds

def RatBounds.sideIntersect (I J : RatBounds) : RatBounds := ⟨max I.lo J.lo, min I.hi J.hi⟩

theorem RatBounds.sideIntersect_mem {I J : RatBounds} {x : ℝ} (hI : I.Contains x) (hJ : J.Contains x) :
    (I.sideIntersect J).Contains x := by
  simpa only [sideIntersect, RatBounds.Contains, Rat.cast_min, Rat.cast_max] using
    And.intro (max_le hI.1 hJ.1) (le_min hI.2 hJ.2)

def SideIntervalInputs.directDiagonal (I : SideIntervalInputs) (i : Fin 2)
    (w arg base : RatBounds) : RatBounds :=
  let P := RatBounds.point
  let r := I.exponent.sub (P 1)
  let first := (I.coefficient i).mul (I.secondPower i)
  let second := (((P 2).mul arg).mul w).mul (I.firstPower i)
  let third := ((((P 2).mul I.a).mul (r.sub (P 1))).mul w).mul (I.secondSlope i)
  ((first.add second).add third).sub ((base.mul base).mul I.scaledSecond)

def SideIntervalInputs.centeredDiagonal (I : SideIntervalInputs) (i : Fin 2)
    (w other arg base : RatBounds) : RatBounds :=
  let P := RatBounds.point
  let r := I.exponent.sub (P 1)
  let signed := (((I.weight 0).add w).sub other).sub (((P 2).mul I.eta).mul base)
  let H := (I.a.mul (I.factor i)).add (arg.mul signed)
  let first := (I.coefficient i).mul ((I.secondPower i).sub (P 1))
  let second := (((P 2).mul arg).mul w).mul ((I.firstPower i).sub (P 1))
  let third := ((((P 2).mul I.a).mul (r.sub (P 1))).mul w).mul (I.secondSlope i)
  (((H.add first).add second).add third).sub ((base.mul base).mul (I.scaledSecond.sub (P 1)))

def SideIntervalInputs.evaluate (I : SideIntervalInputs) : SideCoefficientIntervals :=
  let P := RatBounds.point
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
  let gradient (i : Fin 2) (w base : RatBounds) :=
    I.exponent.mul (((I.factor i).add (((P 2).mul r).mul w)).sub
      (((a₄.mul r).mul base).mul I.baseSlope))
  let diag (i : Fin 2) (w other arg base : RatBounds) :=
    k.mul ((I.directDiagonal i w arg base).sideIntersect (I.centeredDiagonal i w other arg base))
  let mixed := k.mul (((((A.mul (I.weight 2)).mul (I.firstPower 1)).add
    ((B.mul (I.weight 1)).mul (I.firstPower 0))).sub ((C.mul D).mul I.scaledSecond)))
  ⟨constant, gradient 0 (I.weight 1) C, gradient 1 (I.weight 2) D,
    diag 0 (I.weight 1) (I.weight 2) A C, mixed, diag 1 (I.weight 2) (I.weight 1) B D⟩

noncomputable section

private theorem side_point_one : (RatBounds.point 1).Contains (1 : ℝ) := by
  simpa only [Rat.cast_one] using RatBounds.point_mem 1

private theorem side_point_two : (RatBounds.point 2).Contains (2 : ℝ) := by
  simpa only [Rat.cast_ofNat] using RatBounds.point_mem 2

private theorem side_point_four : (RatBounds.point 4).Contains (4 : ℝ) := by
  simpa only [Rat.cast_ofNat] using RatBounds.point_mem 4

private theorem side_point_neg_two : (RatBounds.point (-2)).Contains (-2 : ℝ) := by
  simpa only [Rat.cast_neg, Rat.cast_ofNat] using RatBounds.point_mem (-2)

theorem SideIntervalInputs.evaluate_sound (I : SideIntervalInputs) {q a b η u v : ℝ}
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
  have hr := RatBounds.sub_mem hQ side_point_one
  have hr₁ := RatBounds.sub_mem hr side_point_one
  have hA := RatBounds.sub_mem side_point_one hb
  have hB := RatBounds.add_mem ha hb
  have h2e := RatBounds.mul_mem side_point_two he
  have hC := RatBounds.add_mem side_point_one (RatBounds.mul_mem h2e hA)
  have hD := RatBounds.add_mem side_point_one (RatBounds.mul_mem h2e hB)
  have hJ := RatBounds.sub_mem (RatBounds.sub_mem (hw 0) (hw 1)) (hw 2)
  have hK := RatBounds.mul_mem (RatBounds.mul_mem hQ hr) (RatBounds.point_mem (1 / 2))
  have hK' : ((I.exponent.mul (I.exponent.sub (RatBounds.point 1))).mul
      (RatBounds.point (1/2))).Contains (q * r / 2) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, mul_one_div] using hK
  have h4e := RatBounds.mul_mem side_point_four he
  have hc := RatBounds.sub_mem (RatBounds.mul_mem (RatBounds.mul_mem side_point_neg_two hQ) hJ)
    (RatBounds.mul_mem (RatBounds.mul_mem h4e hQ) hF)
  have gradient {i : Fin 2} {w t g : ℝ} {W T : RatBounds}
      (hw : W.Contains w) (ht : T.Contains t) (hg : (I.factor i).Contains g) :=
    RatBounds.mul_mem hQ
      (RatBounds.sub_mem (RatBounds.add_mem hg (RatBounds.mul_mem (RatBounds.mul_mem side_point_two hr) hw))
        (RatBounds.mul_mem (RatBounds.mul_mem (RatBounds.mul_mem h4e hr) ht) hG))
  let F := Y^(q-2)*sideSecondFactor q t
  have hf : I.scaledSecond.Contains F := hT
  have diagonal {i : Fin 2} {d w o s z n m mr g : ℝ} {Wb O S T : RatBounds}
      (hd : (I.coefficient i).Contains d) (hwj : Wb.Contains w) (hs : S.Contains s) (ht : T.Contains z)
      (hn : (I.firstPower i).Contains n) (hm : (I.secondPower i).Contains m)
      (hmr : (I.secondSlope i).Contains mr) (ho : O.Contains o) (hg : (I.factor i).Contains g)
      (hlinear : d - s * (W 0 - w - o) - z = a*g) (hbase : z = 1+2*η*s) :
      ((((I.exponent.mul (I.exponent.sub (RatBounds.point 1))).mul (RatBounds.point (1/2))).mul
        ((I.directDiagonal i Wb S T).sideIntersect (I.centeredDiagonal i Wb O S T)))).Contains
        (q*r/2*(d*m+2*s*w*n+2*a*(r-1)*w*mr-z*z*F)) := by
    have hslope := RatBounds.mul_mem (RatBounds.mul_mem side_point_two hs) hwj
    have hthird := RatBounds.mul_mem
      (RatBounds.mul_mem (RatBounds.mul_mem (RatBounds.mul_mem side_point_two ha) hr₁) hwj) hmr
    have hsquare := RatBounds.mul_mem ht ht
    have direct := RatBounds.sub_mem (RatBounds.add_mem
      (RatBounds.add_mem (RatBounds.mul_mem hd hm) (RatBounds.mul_mem hslope hn)) hthird)
      (RatBounds.mul_mem hsquare hf)
    have hSigned := RatBounds.sub_mem (RatBounds.sub_mem (RatBounds.add_mem (hw 0) hwj) ho)
      (RatBounds.mul_mem h2e ht)
    have hH := RatBounds.add_mem (RatBounds.mul_mem ha hg) (RatBounds.mul_mem hs hSigned)
    have centered := RatBounds.sub_mem (RatBounds.add_mem
      (RatBounds.add_mem (RatBounds.add_mem hH (RatBounds.mul_mem hd (RatBounds.sub_mem hm side_point_one)))
        (RatBounds.mul_mem hslope (RatBounds.sub_mem hn side_point_one))) hthird)
      (RatBounds.mul_mem hsquare (RatBounds.sub_mem hf side_point_one))
    have heq : a*g+s*(W 0+w-o-2*η*z)+d*(m-1)+2*s*w*(n-1)+2*a*(r-1)*w*mr-z*z*(F-1) =
        d*m+2*s*w*n+2*a*(r-1)*w*mr-z*z*F := by
      linear_combination -hlinear + z*hbase
    rw [heq] at centered
    exact RatBounds.mul_mem hK' (RatBounds.sideIntersect_mem direct centered)
  have hMix := RatBounds.mul_mem hK'
    (RatBounds.sub_mem (RatBounds.add_mem
      (RatBounds.mul_mem (RatBounds.mul_mem hA (hw 2)) hn₂)
      (RatBounds.mul_mem (RatBounds.mul_mem hB (hw 1)) hn₁))
      (RatBounds.mul_mem (RatBounds.mul_mem hC hD) hT))
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
  · simpa only [SideIntervalInputs.evaluate, sideCoefficients, pow_two] using
      diagonal hd₁ (hw 1) hA hC hn₁ hm₁ hmr₁ (hw 2) hg₁ lin₁ rfl
  · exact hMix
  · simpa only [SideIntervalInputs.evaluate, sideCoefficients, pow_two] using
      diagonal hd₂ (hw 2) hB hD hn₂ hm₂ hmr₂ (hw 1) hg₂ lin₂ rfl

end

end HlawkaSchatten.BelowExponent.Vertex
