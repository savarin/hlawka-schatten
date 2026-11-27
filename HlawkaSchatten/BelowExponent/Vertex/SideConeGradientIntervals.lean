/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeIntervals

/-! Interval evaluation of the division-free normalized side gradient. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

structure SideGradientInputs where
  eta : RatBounds
  eps : RatBounds
  direction : Fin 3 → RatBounds
  root : Fin 3 → RatBounds
  betaZero : RatBounds
  betaOne : RatBounds
  betaTwo : RatBounds
  betaLarge : RatBounds

def addThree (f : Fin 3 → RatBounds) : RatBounds := ((f 0).add (f 1)).add (f 2)

def SideGradientInputs.correction (I : SideGradientInputs) : Fin 3 → RatBounds :=
  let P := RatBounds.point
  let T := addThree I.root
  let Δ := fun j => T.sub ((P 2).mul (I.root j))
  let A := fun j => (P 1).sub (I.direction j)
  let B := (I.betaOne.add I.betaTwo).add ((I.eps.mul I.eps).mul I.betaLarge)
  let E := fun j => (P 1).sub (I.eps.mul (A j))
  let weightedRoot (j : Fin 3) (beta : RatBounds) :=
    (beta.mul (I.direction j)).mul (I.eps.add (Δ j))
  let heavyRoot := ((I.eps.mul I.betaLarge).mul ((P 1).sub I.eps)).mul (T.sub I.eps)
  let zeroRoot := I.betaZero.mul (I.eps.add (Δ 0))
  let X := (P (2/3)).mul (((heavyRoot.add zeroRoot).add (weightedRoot 1 I.betaOne)).add
    (weightedRoot 2 I.betaTwo))
  let heavy (j : Fin 3) := ((((P 2).mul I.eps).mul I.betaLarge).mul (I.root j)).mul (E j)
  let apart (j : Fin 3) (R B : RatBounds) := (((P 2).mul (A j)).mul R).mul B
  let c₀ := ((P 0).sub (I.eps.add (Δ 0))).add (((P 2).mul (E 0)).mul B)
  let c₀cross := ((P 2).mul (A 0)).mul ((I.betaOne.mul (I.root 2)).add (I.betaTwo.mul (I.root 1)))
  let c₁ := (((P (-2)).mul (E 1)).mul I.betaOne).add (apart 1 (I.root 2) B)
  let c₂ := (((P (-2)).mul (E 2)).mul I.betaTwo).add (apart 2 (I.root 1) B)
  ![(((c₀.sub (heavy 0)).sub c₀cross).add X),
    (((c₁.sub (heavy 1)).sub (apart 1 I.betaTwo (I.root 0))).add X),
    (((c₂.sub (heavy 2)).sub (apart 2 I.betaOne (I.root 0))).add X)]

def SideGradientInputs.evaluate (I : SideGradientInputs) (j : Fin 3) : RatBounds :=
  (I.correction j).sub ((((RatBounds.point 2).mul I.eta).mul
    ((RatBounds.point 1).sub (I.direction j))).mul (I.correction 0))

noncomputable section

theorem addThree_mem {I : Fin 3 → RatBounds} {x : Row} (h : ∀ i, (I i).Contains (x i)) :
    (addThree I).Contains (∑ i, x i) := by
  rw [Fin.sum_univ_three]
  exact RatBounds.add_mem (RatBounds.add_mem (h 0) (h 1)) (h 2)

set_option maxHeartbeats 400000 in
theorem SideGradientInputs.correction_sound (I : SideGradientInputs) {ε β₀ β₁ β₂ βh : ℝ}
    {e R : Row} (heps : I.eps.Contains ε) (he : ∀ i, (I.direction i).Contains (e i))
    (hR : ∀ i, (I.root i).Contains (R i))
    (hβ₀ : I.betaZero.Contains β₀) (hβ₁ : I.betaOne.Contains β₁)
    (hβ₂ : I.betaTwo.Contains β₂) (hβh : I.betaLarge.Contains βh) (j : Fin 3) :
    (I.correction j).Contains (sideCorrection ε β₀ β₁ β₂ βh e R j) := by
  have one : (RatBounds.point 1).Contains (1 : ℝ) := by simpa using RatBounds.point_mem 1
  have two : (RatBounds.point 2).Contains (2 : ℝ) := by simpa using RatBounds.point_mem 2
  have zero : (RatBounds.point 0).Contains (0 : ℝ) := by simpa using RatBounds.point_mem 0
  have ntwo : (RatBounds.point (-2)).Contains (-2 : ℝ) := by simpa using RatBounds.point_mem (-2)
  have ratio : (RatBounds.point (2/3)).Contains (2/3 : ℝ) := by simpa using RatBounds.point_mem (2/3)
  have hT := addThree_mem hR
  have hΔ (j) := RatBounds.sub_mem hT (RatBounds.mul_mem two (hR j))
  have hA (j) := RatBounds.sub_mem one (he j)
  have hE (j) := RatBounds.sub_mem one (RatBounds.mul_mem heps (hA j))
  have hB := RatBounds.add_mem (RatBounds.add_mem hβ₁ hβ₂)
    (RatBounds.mul_mem (RatBounds.mul_mem heps heps) hβh)
  have hf := RatBounds.mul_mem (RatBounds.mul_mem (RatBounds.mul_mem heps hβh)
    (RatBounds.sub_mem one heps)) (RatBounds.sub_mem hT heps)
  have hx₀ := RatBounds.mul_mem hβ₀ (RatBounds.add_mem heps (hΔ 0))
  have hx₁ := RatBounds.mul_mem (RatBounds.mul_mem hβ₁ (he 1)) (RatBounds.add_mem heps (hΔ 1))
  have hx₂ := RatBounds.mul_mem (RatBounds.mul_mem hβ₂ (he 2)) (RatBounds.add_mem heps (hΔ 2))
  have hX := RatBounds.mul_mem ratio (RatBounds.add_mem (RatBounds.add_mem (RatBounds.add_mem hf hx₀) hx₁) hx₂)
  have heavy (j) := RatBounds.mul_mem (RatBounds.mul_mem (RatBounds.mul_mem (RatBounds.mul_mem two heps)
    hβh) (hR j)) (hE j)
  have apart (j) {B S : RatBounds} {b s : ℝ} (hb : B.Contains b) (hs : S.Contains s) :=
    RatBounds.mul_mem (RatBounds.mul_mem (RatBounds.mul_mem two (hA j)) hb) hs
  have c₀ := RatBounds.add_mem (RatBounds.sub_mem (RatBounds.sub_mem
    (RatBounds.add_mem (RatBounds.sub_mem zero (RatBounds.add_mem heps (hΔ 0)))
      (RatBounds.mul_mem (RatBounds.mul_mem two (hE 0)) hB)) (heavy 0))
    (RatBounds.mul_mem (RatBounds.mul_mem two (hA 0))
      (RatBounds.add_mem (RatBounds.mul_mem hβ₁ (hR 2)) (RatBounds.mul_mem hβ₂ (hR 1))))) hX
  have c₁ := RatBounds.add_mem (RatBounds.sub_mem (RatBounds.sub_mem
    (RatBounds.add_mem (RatBounds.mul_mem (RatBounds.mul_mem ntwo (hE 1)) hβ₁)
      (apart 1 (hR 2) hB)) (heavy 1)) (apart 1 hβ₂ (hR 0))) hX
  have c₂ := RatBounds.add_mem (RatBounds.sub_mem (RatBounds.sub_mem
    (RatBounds.add_mem (RatBounds.mul_mem (RatBounds.mul_mem ntwo (hE 2)) hβ₂)
      (apart 2 (hR 1) hB)) (heavy 2)) (apart 2 hβ₁ (hR 0))) hX
  fin_cases j
  · change (I.correction 0).Contains (sideCorrection ε β₀ β₁ β₂ βh e R 0)
    simpa only [sideCorrection, SideGradientInputs.correction, Matrix.cons_val_zero, pow_two, zero_sub] using c₀
  · change (I.correction 1).Contains (sideCorrection ε β₀ β₁ β₂ βh e R 1)
    simpa only [sideCorrection, SideGradientInputs.correction, Matrix.cons_val_one,
      Matrix.cons_val_zero, pow_two] using c₁
  · change (I.correction 2).Contains (sideCorrection ε β₀ β₁ β₂ βh e R 2)
    simpa only [sideCorrection, SideGradientInputs.correction, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, pow_two] using c₂

theorem SideGradientInputs.evaluate_sound (I : SideGradientInputs) {a b η : ℝ}
    {R : Row}
    (hη : I.eta.Contains η) (hε : I.eps.Contains (η / (1 + 2*η)))
    (he : ∀ i, (I.direction i).Contains (parameterDirection a b i))
    (hR : ∀ i, (I.root i).Contains (R i))
    (hβ₀ : I.betaZero.Contains (beta η (parameterDirection a b) 0))
    (hβ₁ : I.betaOne.Contains (sideBetaFactor η (parameterDirection a b) 1))
    (hβ₂ : I.betaTwo.Contains (sideBetaFactor η (parameterDirection a b) 2))
    (hβh : I.betaLarge.Contains (sideHeavyFactor η (parameterDirection a b))) (j : Fin 3) :
    (I.evaluate j).Contains (sideGradientFactor η (parameterDirection a b) R j) := by
  have one : (RatBounds.point 1).Contains (1 : ℝ) := by simpa using RatBounds.point_mem 1
  have two : (RatBounds.point 2).Contains (2 : ℝ) := by simpa using RatBounds.point_mem 2
  have h i := I.correction_sound hε he hR hβ₀ hβ₁ hβ₂ hβh i
  exact RatBounds.sub_mem (h j) (RatBounds.mul_mem
    (RatBounds.mul_mem (RatBounds.mul_mem two hη) (RatBounds.sub_mem one (he j))) (h 0))

end

end HlawkaSchatten.BelowExponent.Vertex
