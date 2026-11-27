/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonDen

/-! A normalized far secant can be checked on a two-dimensional partition. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

open Vertex (RatBounds)

def unitBox (h a : RatBounds) : Box :=
  ⟨![h.lo, 0, 1, a.lo], ![h.hi, 0, 1, a.hi]⟩

inductive FarTiles
  | leaf (f : FarFactor)
  | height (knot : ℚ) (low high : FarTiles)
  | ratio (knot : ℚ) (low high : FarTiles)

def FarTiles.ok (h a : RatBounds) (cap : ℚ) : FarTiles → Bool
  | .leaf f => f.ok (unitBox h a) true && decide (f.value (unitBox h a) true ≤ cap)
  | .height m l r => l.ok ⟨h.lo,m⟩ a cap && r.ok ⟨m,h.hi⟩ a cap
  | .ratio m l r => l.ok h ⟨a.lo,m⟩ cap && r.ok h ⟨m,a.hi⟩ cap

structure TiledRow where
  sigmaLower : ℕ
  sigmaUpper : ℕ
  jensen : JensenWitness
  left : ℕ
  right : ℕ
  cap : ℚ
  cover : FarTiles

def TiledRow.row (w : TiledRow) : RowWitness :=
  ⟨w.sigmaLower, w.sigmaUpper, w.jensen, .chord .universal w.left w.right⟩

def TiledRow.quad (w : TiledRow) (B : Box) (b : Bool) : Quad :=
  let base := nearTermsCommon B b w.row
  let a := base.squared
  let m := (muBounds B w.row).hi * w.cap
  let p₀ := m * units w.left
  let p₁ := m * units w.right
  let u := B.lo 2
  let width := B.hi 2 - u
  clearDen (a * width^2) ((2*a*u - base.linearCost)*width - (p₁-p₀))
    (a*u^2 - base.linearCost*u + base.constant - p₀)

def TiledRow.okOnRatio (w : TiledRow) (B : Box) (b : Bool) (A : RatBounds) : Bool :=
  decide (Domain B ∧ 0 ≤ w.cap) &&
    G3Power.crossLE (units w.sigmaLower) (B.lo 1) 25 12 &&
    G3Power.crossLE (B.hi 1) (units w.sigmaUpper) 12 25 &&
    w.jensen.ok B &&
    G3Power.tightUpper (B.lo 2) (units w.left) && G3Power.tightUpper (B.hi 2) (units w.right) &&
    w.cover.ok (bounds B 0) A w.cap && (w.quad B b).ok

def TiledRow.ok (w : TiledRow) (B : Box) (b : Bool) : Bool :=
  decide (0 < B.lo 2) && w.okOnRatio B b (signedRatio B b)

inductive TiledCert
  | original (t : CertTree)
  | row (w : TiledRow)
  | cut (j : Fin 4) (knot : ℚ) (lower upper : TiledCert)

def TiledCert.ok (B : Box) (b : Bool) : TiledCert → Bool
  | .original t => t.commonOK B b
  | .row w => w.ok B b
  | .cut j m l r => l.ok (B.lowerChild j m) b && r.ok (B.upperChild j m) b

end HlawkaSchatten.BelowExponent.G3P
