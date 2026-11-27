/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioKernelData

/-! Reuse checked power comparisons only when their complete rational inputs match. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

noncomputable section

open Vertex (RatBounds)

abbrev CrossPowerKey := (ℚ × ℚ) × (Nat × Nat)

def crossPowerKernel (x y : ℚ) (m n : Nat) : Bool :=
  G3Power.Kernel.crossIntLE x.num x.den y.num y.den m n

def upperPowerKernel (x : ℚ) (n : Nat) : Bool :=
  if |x| ≤ 1 then crossPowerKernel x (units n) 1054 665
  else crossPowerKernel x (units n) 485 306

structure PowerCache where
  upper : List (ℚ × Nat)
  cross : List CrossPowerKey

def PowerCache.valid (c : PowerCache) : Bool :=
  c.upper.all (fun e => upperPowerKernel e.1 e.2) &&
    c.cross.all (fun e => crossPowerKernel e.1.1 e.1.2 e.2.1 e.2.2)

def PowerCache.upperCheck (c : PowerCache) (x : ℚ) (n : Nat) : Bool :=
  if c.upper.any (fun e => decide (e = (x,n))) then true else upperPowerKernel x n

def PowerCache.crossCheck (c : PowerCache) (x y : ℚ) (m n : Nat) : Bool :=
  if c.cross.any (fun e => decide (e = ((x,y),(m,n)))) then true
  else crossPowerKernel x y m n

def PowerCache.farCheck (c : PowerCache) (B : Box) (b : Bool) : FarWitness → Bool
  | .chord ff l r => ff.ok B b && c.upperCheck (B.lo 2) l && c.upperCheck (B.hi 2) r
  | .variance q => (FarWitness.variance q).ok B b

def PowerCache.rowCheck (c : PowerCache) (B : Box) (b : Bool) (w : RowWitness) : Bool :=
  decide (Domain B) &&
    c.crossCheck (units w.sigmaLower) (B.lo 1) 25 12 &&
    c.crossCheck (B.hi 1) (units w.sigmaUpper) 12 25 &&
    w.jensen.ok B && c.farCheck B b w.far && (rowQuadRaw B b w).kernelOK

def CertTree.sharedOK (c : PowerCache) (B : Box) (b : Bool) : CertTree → Bool
  | .cone => decide (coneBox B)
  | .empty => decide (B.hi 1 ≤ 1/5 ∧ 1/(2-G3S.kMax B) < B.lo 0)
  | .row w => c.rowCheck B b w
  | .cut j m l r => l.sharedOK c (B.lowerChild j m) b && r.sharedOK c (B.upperChild j m) b

def TiledRow.sharedOKOnRatio (w : TiledRow) (c : PowerCache) (B : Box) (b : Bool)
    (A : RatBounds) : Bool :=
  decide (Domain B ∧ 0 ≤ w.cap) &&
    c.crossCheck (units w.sigmaLower) (B.lo 1) 25 12 &&
    c.crossCheck (B.hi 1) (units w.sigmaUpper) 12 25 &&
    w.jensen.ok B && c.upperCheck (B.lo 2) w.left && c.upperCheck (B.hi 2) w.right &&
    w.cover.ok (bounds B 0) A w.cap && (w.quadRaw B b).kernelOK

def RatioChart.sharedOK (c : PowerCache) (B : Box) (b : Bool) : RatioChart → Bool
  | .original t => decide (B.hi 1 ≤ 1/5 ∧ (lBounds B).hi < 1) &&
      t.sharedOK c (ratioPhysicalBox B b) b
  | .row w => decide (B.hi 1 ≤ 1/5 ∧ (lBounds B).hi < 1) &&
      w.sharedOKOnRatio c (ratioPhysicalBox B b) b (bounds B 3)
  | .cut j m l r => l.sharedOK c (B.lowerChild j m) b && r.sharedOK c (B.upperChild j m) b

def RatioRemainder.sharedOK (c : PowerCache) (B : Box) (b : Bool) (cap : ℚ) :
    RatioRemainder → Bool
  | .original t => t.sharedOK c B b
  | .covered => decide (0 < B.lo 2 ∧ B.hi 1 ≤ 1/5 ∧ (lBounds B).hi ≤ 1 ∧
      (absBounds (center B)).hi ≤ cap * B.lo 2)
  | .cut j m l r => l.sharedOK c (B.lowerChild j m) b cap &&
      r.sharedOK c (B.upperChild j m) b cap

theorem RatioChart.sharedCut_ok {c : PowerCache} {B : Box} {b : Bool}
    {j : Fin 4} {m : ℚ} {l r : RatioChart}
    (hl : l.sharedOK c (B.lowerChild j m) b = true)
    (hr : r.sharedOK c (B.upperChild j m) b = true) :
    (cut j m l r).sharedOK c B b = true := by simp only [sharedOK, hl, hr, Bool.and_self]

theorem RatioRemainder.sharedCut_ok {c : PowerCache} {B : Box} {b : Bool} {cap : ℚ}
    {j : Fin 4} {m : ℚ} {l r : RatioRemainder}
    (hl : l.sharedOK c (B.lowerChild j m) b cap = true)
    (hr : r.sharedOK c (B.upperChild j m) b cap = true) :
    (cut j m l r).sharedOK c B b cap = true := by simp only [sharedOK, hl, hr, Bool.and_self]

end

end HlawkaSchatten.BelowExponent.G3P
