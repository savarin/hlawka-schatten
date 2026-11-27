/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PSharedPowerData
public import HlawkaSchatten.BelowExponent.G3PRatioKernelSound

/-! A checked cache preserves every original ratio and remainder test. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

noncomputable section

open Vertex (RatBounds)

theorem crossPowerKernel_eq (x y : ℚ) (m n : Nat) :
    crossPowerKernel x y m n = G3Power.crossLE x y m n :=
  G3Power.Kernel.crossIntLE_rat_eq x y m n

theorem upperPowerKernel_eq (x : ℚ) (n : Nat) :
    upperPowerKernel x n = G3Power.tightUpper x (units n) := by
  simp only [upperPowerKernel, G3Power.tightUpper, crossPowerKernel_eq]

theorem PowerCache.upperCheck_eq {c : PowerCache} (h : c.valid = true) (x : ℚ) (n : Nat) :
    c.upperCheck x n = G3Power.tightUpper x (units n) := by
  have valid : c.upper.all (fun e => upperPowerKernel e.1 e.2) = true :=
    (Bool.and_eq_true_iff.mp h).1
  unfold upperCheck
  split
  · rename_i hit
    obtain ⟨e, member, matched⟩ := List.any_eq_true.mp hit
    have he : e = (x,n) := of_decide_eq_true matched
    subst e
    have accepted := List.all_eq_true.mp valid (x,n) member
    rw [upperPowerKernel_eq] at accepted
    exact accepted.symm
  · exact upperPowerKernel_eq x n

theorem PowerCache.crossCheck_eq {c : PowerCache} (h : c.valid = true)
    (x y : ℚ) (m n : Nat) : c.crossCheck x y m n = G3Power.crossLE x y m n := by
  have valid : c.cross.all (fun e => crossPowerKernel e.1.1 e.1.2 e.2.1 e.2.2) = true :=
    (Bool.and_eq_true_iff.mp h).2
  unfold crossCheck
  split
  · rename_i hit
    obtain ⟨e, member, matched⟩ := List.any_eq_true.mp hit
    have he : e = ((x,y),(m,n)) := of_decide_eq_true matched
    subst e
    have accepted := List.all_eq_true.mp valid ((x,y),(m,n)) member
    rw [crossPowerKernel_eq] at accepted
    exact accepted.symm
  · exact crossPowerKernel_eq x y m n

theorem PowerCache.farCheck_eq {c : PowerCache} (h : c.valid = true)
    (B : Box) (b : Bool) (w : FarWitness) : c.farCheck B b w = w.ok B b := by
  cases w with
  | chord ff l r => simp only [farCheck, FarWitness.ok, upperCheck_eq h]
  | variance q => rfl

theorem PowerCache.rowCheck_eq {c : PowerCache} (h : c.valid = true)
    (B : Box) (b : Bool) (w : RowWitness) : c.rowCheck B b w = rowOKCommon B b w := by
  simp only [rowCheck, rowOKCommon, crossCheck_eq h, farCheck_eq h,
    Quad.kernelOK_eq, rowQuadRaw_ok_eq]

theorem CertTree.sharedOK_eq {c : PowerCache} (h : c.valid = true)
    (t : CertTree) (B : Box) (b : Bool) : t.sharedOK c B b = t.commonOK B b := by
  induction t generalizing B with
  | cone | empty => rfl
  | row w => exact PowerCache.rowCheck_eq h B b w
  | cut j m l r hl hr => simp only [sharedOK, commonOK, hl, hr]

theorem TiledRow.sharedOKOnRatio_eq {c : PowerCache} (h : c.valid = true)
    (w : TiledRow) (B : Box) (b : Bool) (A : RatBounds) :
    w.sharedOKOnRatio c B b A = w.okOnRatio B b A := by
  simp only [sharedOKOnRatio, okOnRatio, PowerCache.crossCheck_eq h,
    PowerCache.upperCheck_eq h, Quad.kernelOK_eq, quadRaw_ok_eq]

theorem RatioChart.sharedOK_eq {c : PowerCache} (h : c.valid = true)
    (t : RatioChart) (B : Box) (b : Bool) : t.sharedOK c B b = t.ok B b := by
  induction t generalizing B with
  | original t => simp only [sharedOK, ok, CertTree.sharedOK_eq h]
  | row w => simp only [sharedOK, ok, TiledRow.sharedOKOnRatio_eq h]
  | cut j m l r hl hr => simp only [sharedOK, ok, hl, hr]

theorem RatioRemainder.sharedOK_eq {c : PowerCache} (h : c.valid = true)
    (t : RatioRemainder) (B : Box) (b : Bool) (cap : ℚ) :
    t.sharedOK c B b cap = t.ok B b cap := by
  induction t generalizing B with
  | original t => exact CertTree.sharedOK_eq h t B b
  | covered => rfl
  | cut j m l r hl hr => simp only [sharedOK, ok, hl, hr]

theorem RatioChart.ok_of_sharedOK {c : PowerCache} (hc : c.valid = true)
    {t : RatioChart} {B : Box} {b : Bool} (h : t.sharedOK c B b = true) :
    t.ok B b = true := (t.sharedOK_eq hc B b).symm.trans h

theorem RatioRemainder.ok_of_sharedOK {c : PowerCache} (hc : c.valid = true)
    {t : RatioRemainder} {B : Box} {b : Bool} {cap : ℚ}
    (h : t.sharedOK c B b cap = true) : t.ok B b cap = true :=
  (t.sharedOK_eq hc B b cap).symm.trans h

end

end HlawkaSchatten.BelowExponent.G3P
