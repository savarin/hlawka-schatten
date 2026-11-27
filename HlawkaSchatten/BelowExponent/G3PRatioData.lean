/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PFarTiles

/-! Convert a closed box in height, profile ratio, row magnitude and far ratio
to physical coordinates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

open Vertex (RatBounds)

def ratioCenterBounds (B : Box) (b : Bool) : RatBounds :=
  (((point (signRat b)).mul (bounds B 2)).mul (bounds B 3))

def ratioZBounds (B : Box) (b : Bool) : RatBounds :=
  (point 1).add (((ratioCenterBounds B b).sub (point 1)).mul (recip ((point 1).sub (lBounds B))))

def ratioPhysicalBox (B : Box) (b : Bool) : Box :=
  let Z := ratioZBounds B b
  ⟨![B.lo 0, B.lo 1, B.lo 2, Z.lo], ![B.hi 0, B.hi 1, B.hi 2, Z.hi]⟩

def ratioCoverBox (B : Box) (cap : ℚ) : Box :=
  ⟨![B.lo 0, B.lo 1, B.lo 2, -cap], ![B.hi 0, B.hi 1, B.hi 2, cap]⟩

inductive RatioChart
  | original (tree : CertTree)
  | row (w : TiledRow)
  | cut (j : Fin 4) (knot : ℚ) (lower upper : RatioChart)

def RatioChart.ok (B : Box) (b : Bool) : RatioChart → Bool
  | .original t => decide (B.hi 1 ≤ 1/5 ∧ (lBounds B).hi < 1) &&
      t.commonOK (ratioPhysicalBox B b) b
  | .row w => decide (B.hi 1 ≤ 1/5 ∧ (lBounds B).hi < 1) &&
      w.okOnRatio (ratioPhysicalBox B b) b (bounds B 3)
  | .cut j m l r => l.ok (B.lowerChild j m) b && r.ok (B.upperChild j m) b

inductive RatioRemainder
  | original (tree : CertTree)
  | covered
  | cut (j : Fin 4) (knot : ℚ) (lower upper : RatioRemainder)

def RatioRemainder.ok (B : Box) (b : Bool) (cap : ℚ) : RatioRemainder → Bool
  | .original t => t.commonOK B b
  | .covered => decide (0 < B.lo 2 ∧ B.hi 1 ≤ 1/5 ∧ (lBounds B).hi ≤ 1 ∧
      (absBounds (center B)).hi ≤ cap * B.lo 2)
  | .cut j m l r => l.ok (B.lowerChild j m) b cap && r.ok (B.upperChild j m) b cap

theorem RatioChart.cut_ok {B : Box} {b : Bool} {j : Fin 4} {m : ℚ} {l r : RatioChart}
    (hl : l.ok (B.lowerChild j m) b = true) (hr : r.ok (B.upperChild j m) b = true) :
    (cut j m l r).ok B b = true := by simp only [ok, hl, hr, Bool.and_self]

theorem RatioRemainder.cut_ok {B : Box} {b : Bool} {cap : ℚ} {j : Fin 4} {m : ℚ}
    {l r : RatioRemainder} (hl : l.ok (B.lowerChild j m) b cap = true)
    (hr : r.ok (B.upperChild j m) b cap = true) : (cut j m l r).ok B b cap = true := by
  simp only [ok, hl, hr, Bool.and_self]

end HlawkaSchatten.BelowExponent.G3P
