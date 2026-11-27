/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.RatKernel
public import HlawkaSchatten.BelowExponent.G3PSharedPowerData
public import HlawkaSchatten.BelowExponent.G3PPreparedNearData

/-! G3 geometry in exact fractions, with normalization at power and polynomial boundaries. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P.Geometry

open Vertex (RatK RatBoundsK RatBounds)

noncomputable section

def neg (x : RatK) : RatK := RatK.zero.sub x
def abs (x : RatK) : RatK := x.maxK (neg x)
def half : RatK := RatK.ofRat (1/2)
def unit (n : Nat) : RatK := ⟨Int.ofNat n, 274877906943⟩
def sign (b : Bool) : RatK := bif b then RatK.one else RatK.negOne

theorem ratOfK_reduced (x : RatK) : x.reduce.num.natAbs.Coprime (x.reduce.pred + 1) := by
  rw [RatK.reduce_eq]
  simp only [RatK.ofRat]
  rw [Nat.sub_add_cancel x.val.den_pos]
  exact x.val.reduced

/-- `x.val` built from the fields of `x.reduce`: the kernel takes one gcd instead of normalizing
a rational division. `ratOfK_eq` gives `ratOfK x = x.val`, so the fields are those of `x.val`. -/
def ratOfK (x : RatK) : ℚ :=
  ⟨x.reduce.num, x.reduce.pred + 1, Nat.succ_ne_zero _, ratOfK_reduced x⟩

/-- `A.val` with both endpoints built by `ratOfK`. -/
def boundsOfK (A : RatBoundsK) : RatBounds := ⟨ratOfK A.lo, ratOfK A.hi⟩

/-- `unitBox h a` with each coordinate selected by a Boolean test instead of `![...]`. -/
def unitBoxK (h a : RatBounds) : Box :=
  ⟨fun k => Bool.rec (Bool.rec (Bool.rec a.lo 1 (Nat.beq k.val 2)) 0 (Nat.beq k.val 1)) h.lo
      (Nat.beq k.val 0),
    fun k => Bool.rec (Bool.rec (Bool.rec a.hi 1 (Nat.beq k.val 2)) 0 (Nat.beq k.val 1)) h.hi
      (Nat.beq k.val 0)⟩

/-- The rational `3/20` and `49/50` as kernel fractions. -/
def threeTwentieths : RatK := ⟨3, 19⟩
def fortyNineFiftieths : RatK := ⟨49, 49⟩
def interval (B : Box) (j : Fin 4) : RatBoundsK := RatBoundsK.ofRat (bounds B j)

/-- `(RatBoundsK.point c).mul X`, computed from its two distinct products (`pointMul_eq`). -/
def pointMul (c : RatK) (X : RatBoundsK) : RatBoundsK :=
  let p := c.mul X.lo
  let q := c.mul X.hi
  ⟨p.minK q, p.maxK q⟩

/-- `A.mul B`, taking only `A.lo*B.lo` and `A.hi*B.hi` when both intervals are nonnegative and
ordered: then each comparison of the four products holds and selects exactly those two
(`mulNonneg_eq`). The sign tests come first. -/
def mulNonneg (A B : RatBoundsK) : RatBoundsK :=
  Bool.rec (A.mul B) ⟨A.lo.mul B.lo, A.hi.mul B.hi⟩
    (Bool.rec false (Bool.rec false (Bool.rec false (B.lo.le B.hi) (A.lo.le A.hi))
      (Vertex.intNonnegK B.lo.num)) (Vertex.intNonnegK A.lo.num))

/-- `X.mul (RatBoundsK.point c)`, computed from its two distinct products (`mulPoint_eq`). -/
def mulPoint (X : RatBoundsK) (c : RatK) : RatBoundsK :=
  let p := X.lo.mul c
  let q := X.hi.mul c
  ⟨p.minK q, p.maxK q⟩
def reciprocal (A : RatBoundsK) : RatBoundsK := ⟨A.hi.inv, A.lo.inv⟩
def absolute (A : RatBoundsK) : RatBoundsK :=
  ⟨RatK.zero.maxK (A.lo.maxK (neg A.hi)), (abs A.lo).maxK (abs A.hi)⟩
def ratio (x : ℚ) : RatK := (RatK.ofRat x).mul (RatK.two.sub (RatK.ofRat x)).inv
def kBounds (B : Box) : RatBoundsK := ⟨ratio (B.lo 1), ratio (B.hi 1)⟩
def lBounds (B : Box) : RatBoundsK := mulNonneg (interval B 0) (kBounds B)

def center (B : Box) : RatBoundsK :=
  let L := lBounds B
  let zk (z : ℚ) := (RatBoundsK.point (RatK.ofRat z)).add
    (pointMul (RatK.one.sub (RatK.ofRat z)) L)
  ⟨(zk (B.lo 3)).lo, (zk (B.hi 3)).hi⟩

def signedRatio (B : Box) (b : Bool) : RatBoundsK :=
  (pointMul (sign b) (center B)).mul (reciprocal (interval B 2))

def ratioCenter (B : Box) (b : Bool) : RatBoundsK :=
  (pointMul (sign b) (interval B 2)).mul (interval B 3)

def ratioZ (B : Box) (b : Bool) : RatBoundsK :=
  (RatBoundsK.point RatK.one).add
    (((ratioCenter B b).sub (RatBoundsK.point RatK.one)).mul
      (reciprocal ((RatBoundsK.point RatK.one).sub (lBounds B))))

def physicalBox (B : Box) (b : Bool) : Box :=
  let Z := ratioZ B b
  ⟨fun k => Bool.rec (B.lo k) (ratOfK Z.lo) (Nat.beq k.val 3),
    fun k => Bool.rec (B.hi k) (ratOfK Z.hi) (Nat.beq k.val 3)⟩

def jensenBase (B : Box) : RatK :=
  (RatK.one.maxK (RatK.ofRat (B.lo 3))).minK (RatK.ofRat (B.hi 3))

def jensenShift (B : Box) : RatK :=
  let z := jensenBase B
  z.add ((lBounds B).hi.mul (RatK.one.sub z))

def coefficient (h : ℚ) : RatK :=
  (RatK.ofRat (3/5)).mul (RatK.one.add ((RatK.ofRat h).mul (RatK.ofRat (1/16))))

def muBounds (B : Box) (w : RowWitness) : RatBoundsK :=
  let lo : RatK := Bool.rec fortyNineFiftieths RatK.one ((RatK.ofRat (B.hi 1)).lt threeTwentieths)
  let hi : RatK := Bool.rec fortyNineFiftieths RatK.one ((RatK.ofRat (B.lo 1)).lt threeTwentieths)
  ⟨(lo.mul (coefficient (B.lo 0))).mul (unit w.sigmaLower),
    (hi.mul (coefficient (B.hi 0))).mul (unit w.sigmaUpper)⟩

def jensenValue (B : Box) : JensenWitness → RatK
  | .zero => RatK.zero
  | .direct f g =>
    let L := (lBounds B).hi
    let total := ((RatK.one.sub L).mul (unit f)).add L
    (total.sub (unit g)).mul L.inv

def cross (x y : RatK) (m n : Nat) : Bool := x.reduce.crossLE y.reduce m n

def tightLower (x : RatK) (n : Nat) : Bool :=
  Bool.rec (cross (unit n) x 665 1054) (cross (unit n) x 306 485)
    ((abs x).le RatK.one)

def tightUpper (x : RatK) (n : Nat) : Bool :=
  Bool.rec (cross x (unit n) 485 306) (cross x (unit n) 1054 665)
    ((abs x).le RatK.one)

def tightCurve (x : RatK) (n : Nat) : Bool :=
  Bool.rec (cross x.inv (unit n) 127 306) (cross x.inv (unit n) 276 665)
    (x.le RatK.one)

def predLower (x : RatK) (n : Nat) : Bool :=
  Bool.rec (cross (unit n) x 665 389) (cross (unit n) x 306 179)
    (x.le RatK.one)

def predUpper (x : RatK) (n : Nat) : Bool :=
  Bool.rec (cross x (unit n) 179 306) (cross x (unit n) 389 665)
    (x.le RatK.one)

def jensenOK (B : Box) : JensenWitness → Bool
  | .zero => true
  | .direct f g => tightLower (jensenBase B) f && tightUpper (jensenShift B) g

def slopeGain (w : MidpointWitness) : RatK :=
  ((RatK.ofRat qBounds.hi).mul ((RatK.ofRat qBounds.hi).sub RatK.one)).mul (unit w.curvature)

def slopeLoss (w : MidpointWitness) : RatK :=
  ((RatK.ofRat qBounds.lo).mul half).mul ((unit w.yLower).add (unit w.twoMinusYLower))

def midpointOK (B : Box) (b : Bool) (w : MidpointWitness) : Bool :=
  let A := signedRatio B b
  let y := A.lo.add (RatK.ofRat (B.lo 0))
  let m := A.lo.add ((RatK.ofRat (B.lo 0)).mul half)
  let ymax := A.hi.add (RatK.ofRat (B.hi 0))
  (RatK.zero.lt (RatK.ofRat (B.lo 2)) && RatK.zero.le A.lo &&
    RatK.zero.lt y && RatK.zero.lt m && ymax.lt RatK.two) &&
    tightUpper (y.sub RatK.two) w.pairHigh && tightLower y w.pairLow &&
    predUpper m w.midUpper && tightCurve m w.curvature &&
    predLower y w.yLower && predLower (RatK.two.sub ymax) w.twoMinusYLower

def midpointValue (B : Box) (b : Bool) (w : MidpointWitness) : RatK :=
  let A := signedRatio B b
  let D := slopeGain w
  let L := slopeLoss w
  let start := (((unit w.pairHigh).sub (unit w.pairLow)).mul half).add
    ((RatK.ofRat qBounds.hi).mul (unit w.midUpper))
  let middle := start.add ((RatK.zero.maxK (D.sub L)).mul (A.hi.sub A.lo))
  RatK.zero.maxK (middle.add ((RatK.zero.maxK ((D.mul half).sub L)).mul
    ((RatK.ofRat (B.hi 0)).sub (RatK.ofRat (B.lo 0)))))

def farOK (B : Box) (b : Bool) : FarFactor → Bool
  | .universal => true
  | .secant p q r s =>
    let A := signedRatio B b
    let x := A.lo.add (RatK.ofRat (B.lo 0))
    RatK.zero.lt (RatK.ofRat (B.lo 2)) &&
      tightUpper (x.sub RatK.two) p && tightLower x q &&
      tightUpper (A.hi.add (RatK.ofRat (B.hi 0))) r && tightLower A.hi s
  | .midpoint w => midpointOK B b w

def farValue (B : Box) (b : Bool) : FarFactor → RatK
  | .universal => RatK.two
  | .secant p q r s => RatK.zero.maxK
    ((((unit p).sub (unit q)).mul half).add
      (((unit r).sub (unit s)).mul (RatK.ofRat (B.hi 0)).inv))
  | .midpoint w => midpointValue B b w

def farWitnessOK (c : PowerCache) (B : Box) (b : Bool) : FarWitness → Bool
  | .chord ff l r => farOK B b ff && c.upperCheck (B.lo 2) l && c.upperCheck (B.hi 2) r
  | .variance n => RatK.zero.lt (absolute (center B)).lo &&
      tightCurve (absolute (center B)).lo n

def farTilesOK (h a : RatBounds) (cap : ℚ) : FarTiles → Bool
  | .leaf f => farOK (unitBoxK h a) true f &&
      (farValue (unitBoxK h a) true f).le (RatK.ofRat cap)
  | .height m l r => farTilesOK ⟨h.lo,m⟩ a cap l && farTilesOK ⟨m,h.hi⟩ a cap r
  | .ratio m l r => farTilesOK h ⟨a.lo,m⟩ cap l && farTilesOK h ⟨m,a.hi⟩ cap r

def varianceCost (B : Box) (w : RowWitness) (n : Nat) : RatBoundsK :=
  (mulPoint (mulNonneg (muBounds B w) (RatBoundsK.ofRat qBounds)) half).mul
    (mulPoint ((RatBoundsK.point RatK.two).sub (interval B 0)) (unit n))

def chordCosts (B : Box) (b : Bool) (w : RowWitness) : RatK × RatK :=
  match w.far with
  | .chord ff l r =>
    let F := (muBounds B w).hi.mul (farValue B b ff)
    (F.mul (unit l), F.mul (unit r))
  | .variance _ => (RatK.zero, RatK.zero)

def preparedNear (B : Box) (w : RowWitness) : PreparedNear :=
  let K := CommonDen.Kernel.ofBounds (boundsOfK (kBounds B))
  let W := CommonDen.Kernel.mul K (CommonDen.Kernel.sub
    (CommonDen.Kernel.ofBounds (bounds B 3)) (CommonDen.ofRat 1))
  ⟨CommonDen.Kernel.ofBounds (bounds B 0), CommonDen.Kernel.ofBounds (bounds B 2),
    K, W, CommonDen.Kernel.ofBounds (boundsOfK (muBounds B w)),
    RawScalar.ofRat (ratOfK (jensenValue B w.jensen))⟩

def nearRaw (B : Box) (b : Bool) (w : RowWitness) : RawLowerPolynomial :=
  nearRawPrepared b (preparedNear B w)

def rowQuad (B : Box) (b : Bool) (w : RowWitness) : Quad :=
  let adjustment := match w.far with
    | .chord .. => RawScalar.ofRat 0
    | .variance n => RawScalar.ofRat (ratOfK (varianceCost B w n).hi)
  let costs := chordCosts B b w
  let u := RawScalar.ofRat (B.lo 2)
  (nearRaw B b w).quad adjustment u (RawScalar.sub (RawScalar.ofRat (B.hi 2)) u)
    (RawScalar.ofRat (ratOfK costs.1)) (RawScalar.ofRat (ratOfK costs.2))

def tiledQuad (w : TiledRow) (B : Box) (b : Bool) : Quad :=
  let m := RawScalar.mul (RawScalar.ofRat (ratOfK (muBounds B w.row).hi)) (RawScalar.ofRat w.cap)
  let p0 := RawScalar.mul m (RawScalar.ofRat (ratOfK (unit w.left)))
  let p1 := RawScalar.mul m (RawScalar.ofRat (ratOfK (unit w.right)))
  let u := RawScalar.ofRat (B.lo 2)
  (nearRaw B b w.row).quad (RawScalar.ofRat 0) u
    (RawScalar.sub (RawScalar.ofRat (B.hi 2)) u) p0 p1

def domainOK (B : Box) : Bool :=
  let H := interval B 0
  let S := interval B 1
  let U := interval B 2
  let L := (lBounds B).hi
  RatK.zero.le H.lo && RatK.zero.lt H.hi && H.hi.le (RatK.ofRat (9/17)) &&
    RatK.zero.lt S.lo && S.hi.le (RatK.ofRat (1/5)) && RatK.zero.lt L && L.le RatK.one &&
    RatK.zero.le U.lo && U.lo.lt U.hi && U.hi.le RatK.one

end

end HlawkaSchatten.BelowExponent.G3P.Geometry
