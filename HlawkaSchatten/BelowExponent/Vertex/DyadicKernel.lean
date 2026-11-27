/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck
public import HlawkaSchatten.BelowExponent.Vertex.RatKernel

/-! Kernel-reduction forms of the fixed-point interval operations. Products, sums and comparisons
run on Lean 4.37's `Int.*_k` operations and `Nat` primitives, and each is proved equal to the
operation it replaces, for all inputs. Shared by the families whose checkers evaluate `DyadicBounds`
in the kernel. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

namespace DyadicBounds

/-- `DyadicBounds.mul` on kernel integer operations. -/
noncomputable def mulK (a b : DyadicBounds) : DyadicBounds :=
  let p1 := Int.mul_k a.lo b.lo
  let p2 := Int.mul_k a.lo b.hi
  let p3 := Int.mul_k a.hi b.lo
  let p4 := Int.mul_k a.hi b.hi
  ⟨Int.ediv_k (intMinK (intMinK p1 p2) (intMinK p3 p4)) (Int.ofNat 79228162514264337593543950336),
    Int.neg_k (Int.ediv_k (Int.neg_k (intMaxK (intMaxK p1 p2) (intMaxK p3 p4)))
      (Int.ofNat 79228162514264337593543950336)), a.ok && b.ok⟩

theorem mulK_eq (a b : DyadicBounds) : a.mulK b = a.mul b := rfl

/-- `DyadicBounds.add` and `DyadicBounds.sub` on kernel integer operations. -/
noncomputable def addK (a b : DyadicBounds) : DyadicBounds :=
  ⟨Int.add_k a.lo b.lo, Int.add_k a.hi b.hi, a.ok && b.ok⟩

noncomputable def subK (a b : DyadicBounds) : DyadicBounds :=
  ⟨Int.sub_k a.lo b.hi, Int.sub_k a.hi b.lo, a.ok && b.ok⟩

theorem addK_eq (a b : DyadicBounds) : a.addK b = a.add b := rfl

theorem subK_eq (a b : DyadicBounds) : a.subK b = a.sub b := rfl

/-- `lowerOK` and `upperOK` by integer cross-multiplication, using `0 < q.den` and `0 < units`. -/
noncomputable def lowerOKK (a : DyadicBounds) (q : ℚ) : Bool :=
  a.ok && intNonnegK (Int.sub_k (Int.mul_k a.lo (Int.ofNat q.den))
    (Int.mul_k q.num (Int.ofNat 79228162514264337593543950336)))

noncomputable def upperOKK (a : DyadicBounds) (q : ℚ) : Bool :=
  a.ok && intNonnegK (Int.sub_k (Int.mul_k q.num (Int.ofNat 79228162514264337593543950336))
    (Int.mul_k a.hi (Int.ofNat q.den)))

theorem lowerOKK_eq (a : DyadicBounds) (q : ℚ) : a.lowerOKK q = a.lowerOK q := rfl

theorem upperOKK_eq (a : DyadicBounds) (q : ℚ) : a.upperOKK q = a.upperOK q := rfl

/-- `DyadicBounds.point 1` as a literal. -/
def oneK : DyadicBounds :=
  ⟨Int.ofNat 79228162514264337593543950336, Int.ofNat 79228162514264337593543950336, true⟩

theorem oneK_eq : oneK = point 1 := by decide +kernel

/-- `DyadicBounds.intersect` on kernel integer operations. -/
noncomputable def intersectK (a b : DyadicBounds) : DyadicBounds :=
  ⟨intMaxK a.lo b.lo, intMinK a.hi b.hi, a.ok && b.ok⟩

theorem intersectK_eq (a b : DyadicBounds) : a.intersectK b = a.intersect b := rfl

end DyadicBounds

namespace RatK

/-- `2 ^ 96`, the fixed-point scale. -/
def unitsK : RatK := ⟨Int.ofNat 79228162514264337593543950336, 0⟩

theorem val_unitsK : unitsK.val = ((DyadicBounds.units : ℕ) : ℚ) := by
  simp only [val, unitsK, DyadicBounds.units, Int.ofNat_eq_natCast]; norm_num

end RatK

namespace RatBoundsK

/-- `DyadicBounds.ofRat` on kernel integer operations. -/
noncomputable def toDyadic (a : RatBoundsK) : DyadicBounds :=
  ⟨(a.lo.mul RatK.unitsK).floor, (a.hi.mul RatK.unitsK).ceil, true⟩

theorem toDyadic_eq (a : RatBoundsK) : a.toDyadic = DyadicBounds.ofRat a.val := by
  simp [toDyadic, DyadicBounds.ofRat_def, val, RatK.floor_eq, RatK.ceil_eq, RatK.val_mul,
    RatK.val_unitsK]

end RatBoundsK

end HlawkaSchatten.BelowExponent.Vertex
