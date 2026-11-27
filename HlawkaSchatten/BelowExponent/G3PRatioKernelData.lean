/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioData
public import HlawkaSchatten.BelowExponent.G3PCommonKernelData

/-! The ratio checker with unreduced polynomial coefficients and native integer tests. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

noncomputable section

open Vertex (RatBounds)

def TiledRow.quadRaw (w : TiledRow) (B : Box) (b : Bool) : Quad :=
  let base := nearTermsRaw B b w.row
  let m := RawScalar.mul (RawScalar.ofRat (muBounds B w.row).hi) (RawScalar.ofRat w.cap)
  let p0 := RawScalar.mul m (RawScalar.ofRat (units w.left))
  let p1 := RawScalar.mul m (RawScalar.ofRat (units w.right))
  let u := RawScalar.ofRat (B.lo 2)
  let width := RawScalar.sub (RawScalar.ofRat (B.hi 2)) u
  base.quad (RawScalar.ofRat 0) u width p0 p1

def TiledRow.kernelOKOnRatio (w : TiledRow) (B : Box) (b : Bool) (A : RatBounds) : Bool :=
  decide (Domain B ∧ 0 ≤ w.cap) &&
    G3Power.Kernel.crossIntLE (units w.sigmaLower).num (units w.sigmaLower).den
      (B.lo 1).num (B.lo 1).den 25 12 &&
    G3Power.Kernel.crossIntLE (B.hi 1).num (B.hi 1).den
      (units w.sigmaUpper).num (units w.sigmaUpper).den 12 25 &&
    w.jensen.ok B &&
    G3Power.tightUpper (B.lo 2) (units w.left) && G3Power.tightUpper (B.hi 2) (units w.right) &&
    w.cover.ok (bounds B 0) A w.cap && (w.quadRaw B b).kernelOK

def RatioChart.kernelOK (B : Box) (b : Bool) : RatioChart → Bool
  | .original t => decide (B.hi 1 ≤ 1/5 ∧ (lBounds B).hi < 1) &&
      t.kernelOK (ratioPhysicalBox B b) b
  | .row w => decide (B.hi 1 ≤ 1/5 ∧ (lBounds B).hi < 1) &&
      w.kernelOKOnRatio (ratioPhysicalBox B b) b (bounds B 3)
  | .cut j m l r => l.kernelOK (B.lowerChild j m) b && r.kernelOK (B.upperChild j m) b

def RatioRemainder.kernelOK (B : Box) (b : Bool) (cap : ℚ) : RatioRemainder → Bool
  | .original t => t.kernelOK B b
  | .covered => decide (0 < B.lo 2 ∧ B.hi 1 ≤ 1/5 ∧ (lBounds B).hi ≤ 1 ∧
      (absBounds (center B)).hi ≤ cap * B.lo 2)
  | .cut j m l r => l.kernelOK (B.lowerChild j m) b cap && r.kernelOK (B.upperChild j m) b cap

theorem RatioChart.kernelCut_ok {B : Box} {b : Bool} {j : Fin 4} {m : ℚ} {l r : RatioChart}
    (hl : l.kernelOK (B.lowerChild j m) b = true)
    (hr : r.kernelOK (B.upperChild j m) b = true) :
    (cut j m l r).kernelOK B b = true := by simp only [kernelOK, hl, hr, Bool.and_self]

theorem RatioRemainder.kernelCut_ok {B : Box} {b : Bool} {cap : ℚ} {j : Fin 4} {m : ℚ}
    {l r : RatioRemainder} (hl : l.kernelOK (B.lowerChild j m) b cap = true)
    (hr : r.kernelOK (B.upperChild j m) b cap = true) :
    (cut j m l r).kernelOK B b cap = true := by simp only [kernelOK, hl, hr, Bool.and_self]

end

end HlawkaSchatten.BelowExponent.G3P
