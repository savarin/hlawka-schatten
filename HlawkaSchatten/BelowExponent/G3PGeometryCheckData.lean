/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PGeometryData

/-! Ratio and remainder checking through exact native geometry. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

noncomputable section

open Vertex (RatK RatBounds)

/-- `q` rebuilt by matching on it; equal to `q`. The kernel evaluates the matched `q` as a
recursor's major premise, a result it caches, and the rebuilt value carries `q`'s evaluated fields,
so a parent coordinate or cut knot that many leaves share is evaluated once. -/
def rereadRat (q : ℚ) : ℚ := Rat.rec (motive := fun _ => ℚ) (fun n d h r => ⟨n, d, h, r⟩) q

theorem rereadRat_eq (q : ℚ) : rereadRat q = q := by cases q; rfl

/-- `B.lowerChild j m` with a Boolean coordinate test and every coordinate reread. -/
def Box.lowerChildK (B : Box) (j : Fin 4) (m : ℚ) : Box :=
  ⟨fun k => rereadRat (B.lo k),
    fun k => Bool.rec (rereadRat (B.hi k)) (rereadRat m) (Nat.beq k.val j.val)⟩

/-- `B.upperChild j m` with a Boolean coordinate test and every coordinate reread. -/
def Box.upperChildK (B : Box) (j : Fin 4) (m : ℚ) : Box :=
  ⟨fun k => Bool.rec (rereadRat (B.lo k)) (rereadRat m) (Nat.beq k.val j.val),
    fun k => rereadRat (B.hi k)⟩

theorem Box.lowerChildK_eq (B : Box) (j : Fin 4) (m : ℚ) :
    B.lowerChildK j m = B.lowerChild j m := by
  unfold Box.lowerChildK Box.lowerChild
  congr 1
  funext k
  cases hb : Nat.beq k.val j.val
  · have h : k ≠ j := fun e => Nat.ne_of_beq_eq_false hb (congrArg Fin.val e)
    simp [h, rereadRat_eq]
  · have h : k = j := Fin.ext (Nat.eq_of_beq_eq_true hb)
    simp [h, rereadRat_eq]

theorem Box.upperChildK_eq (B : Box) (j : Fin 4) (m : ℚ) :
    B.upperChildK j m = B.upperChild j m := by
  unfold Box.upperChildK Box.upperChild
  congr 1
  funext k
  cases hb : Nat.beq k.val j.val
  · have h : k ≠ j := fun e => Nat.ne_of_beq_eq_false hb (congrArg Fin.val e)
    simp [h, rereadRat_eq]
  · have h : k = j := Fin.ext (Nat.eq_of_beq_eq_true hb)
    simp [h, rereadRat_eq]

def PowerCache.geometryRowCheck (c : PowerCache) (B : Box) (b : Bool) (w : RowWitness) : Bool :=
  Geometry.domainOK B &&
    c.crossCheck (Geometry.ratOfK (Geometry.unit w.sigmaLower)) (B.lo 1) 25 12 &&
    c.crossCheck (B.hi 1) (Geometry.ratOfK (Geometry.unit w.sigmaUpper)) 12 25 &&
    Geometry.jensenOK B w.jensen && Geometry.farWitnessOK c B b w.far &&
    (Geometry.rowQuad B b w).kernelOK

def CertTree.geometryOK (c : PowerCache) (B : Box) (b : Bool) : CertTree → Bool
  | .cone => decide (coneBox B)
  | .empty => decide (B.hi 1 ≤ 1/5 ∧ 1/(2-G3S.kMax B) < B.lo 0)
  | .row w => c.geometryRowCheck B b w
  | .cut j m l r => l.geometryOK c (B.lowerChildK j m) b &&
      r.geometryOK c (B.upperChildK j m) b

def TiledRow.geometryOKOnRatio (w : TiledRow) (c : PowerCache) (B : Box) (b : Bool)
    (A : RatBounds) : Bool :=
  (Geometry.domainOK B && RatK.zero.le (RatK.ofRat w.cap)) &&
    c.crossCheck (Geometry.ratOfK (Geometry.unit w.sigmaLower)) (B.lo 1) 25 12 &&
    c.crossCheck (B.hi 1) (Geometry.ratOfK (Geometry.unit w.sigmaUpper)) 12 25 &&
    Geometry.jensenOK B w.jensen && c.upperCheck (B.lo 2) w.left &&
    c.upperCheck (B.hi 2) w.right && Geometry.farTilesOK (bounds B 0) A w.cap w.cover &&
    (Geometry.tiledQuad w B b).kernelOK

def geometryChartGuard (B : Box) : Bool :=
  (RatK.ofRat (B.hi 1)).le (RatK.ofRat (1/5)) && (Geometry.lBounds B).hi.lt RatK.one

def geometryCoveredGuard (B : Box) (cap : ℚ) : Bool :=
  RatK.zero.lt (RatK.ofRat (B.lo 2)) &&
    (RatK.ofRat (B.hi 1)).le (RatK.ofRat (1/5)) &&
    (Geometry.lBounds B).hi.le RatK.one &&
    (Geometry.absolute (Geometry.center B)).hi.le
      ((RatK.ofRat cap).mul (RatK.ofRat (B.lo 2)))

def RatioChart.geometryOK (c : PowerCache) (B : Box) (b : Bool) : RatioChart → Bool
  | .original t => geometryChartGuard B && t.geometryOK c (Geometry.physicalBox B b) b
  | .row w => geometryChartGuard B &&
      w.geometryOKOnRatio c (Geometry.physicalBox B b) b (bounds B 3)
  | .cut j m l r => l.geometryOK c (B.lowerChildK j m) b &&
      r.geometryOK c (B.upperChildK j m) b

def RatioRemainder.geometryOK (c : PowerCache) (B : Box) (b : Bool) (cap : ℚ) :
    RatioRemainder → Bool
  | .original t => t.geometryOK c B b
  | .covered => geometryCoveredGuard B cap
  | .cut j m l r => l.geometryOK c (B.lowerChildK j m) b cap &&
      r.geometryOK c (B.upperChildK j m) b cap

theorem CertTree.geometryCut_ok {c : PowerCache} {B : Box} {b : Bool}
    {j : Fin 4} {m : ℚ} {l r : CertTree}
    (hl : l.geometryOK c (B.lowerChild j m) b = true)
    (hr : r.geometryOK c (B.upperChild j m) b = true) :
    (cut j m l r).geometryOK c B b = true := by
  simp only [geometryOK, Box.lowerChildK_eq, Box.upperChildK_eq, hl, hr, Bool.and_self]

theorem RatioChart.geometryCut_ok {c : PowerCache} {B : Box} {b : Bool}
    {j : Fin 4} {m : ℚ} {l r : RatioChart}
    (hl : l.geometryOK c (B.lowerChild j m) b = true)
    (hr : r.geometryOK c (B.upperChild j m) b = true) :
    (cut j m l r).geometryOK c B b = true := by
  simp only [geometryOK, Box.lowerChildK_eq, Box.upperChildK_eq, hl, hr, Bool.and_self]

theorem RatioRemainder.geometryCut_ok {c : PowerCache} {B : Box} {b : Bool} {cap : ℚ}
    {j : Fin 4} {m : ℚ} {l r : RatioRemainder}
    (hl : l.geometryOK c (B.lowerChild j m) b cap = true)
    (hr : r.geometryOK c (B.upperChild j m) b cap = true) :
    (cut j m l r).geometryOK c B b cap = true := by
  simp only [geometryOK, Box.lowerChildK_eq, Box.upperChildK_eq, hl, hr, Bool.and_self]

end

end HlawkaSchatten.BelowExponent.G3P
