/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PData
public import HlawkaSchatten.BelowExponent.G3Power

/-! Exact rational arithmetic for the adaptive transverse G3 certificates. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3S

abbrev Box := G3P.Box

def mulLo (a₀ a₁ b₀ b₁ : ℚ) : ℚ :=
  min (min (a₀ * b₀) (a₀ * b₁)) (min (a₁ * b₀) (a₁ * b₁))

def mulHi (a₀ a₁ b₀ b₁ : ℚ) : ℚ :=
  max (max (a₀ * b₀) (a₀ * b₁)) (max (a₁ * b₀) (a₁ * b₁))

def ratio (s : ℚ) : ℚ := s / (2 - s)

def kMin (B : Box) : ℚ := ratio (B.lo 1)
def kMax (B : Box) : ℚ := ratio (B.hi 1)
def aMin (B : Box) : ℚ :=
  max 0 (1 + mulLo (kMin B) (kMax B) (B.lo 2 - B.hi 3) (B.hi 2 - B.lo 3))
def aMax (B : Box) : ℚ :=
  1 + mulHi (kMin B) (kMax B) (B.lo 2 - B.hi 3) (B.hi 2 - B.lo 3)
def pathMax (B : Box) : ℚ := B.hi 0 * aMax B
def farBase (B : Box) : ℚ := B.lo 3 + B.lo 0 * aMin B
def rowAbsMax (B : Box) : ℚ := max |B.lo 3| |B.hi 3|

structure Witness where
  left : Nat
  right : Nat
  leftShift : Nat
  rightShift : Nat
  farShift : Nat
  farStart : Nat
  pairShift : Nat
  pairStart : Nat
  zPower : Nat
  σLower : Nat
  σUpper : Nat

def units (n : Nat) : ℚ := (n : ℚ) / 268435456

def nearSlope (B : Box) (w : Witness) : ℚ :=
  (units w.left + units w.right - units w.leftShift - units w.rightShift) / (2 * pathMax B)

def farSlope (B : Box) (w : Witness) : ℚ :=
  (units w.farShift - units w.farStart) / pathMax B

def core (w : Witness) : ℚ := (units w.left + units w.right) / 2 - units w.zPower

def coefficient (h : ℚ) : ℚ := (3 / 5) * (1 + h / 16)

def weightLower (B : Box) (lo : ℚ) : ℚ :=
  (if B.hi 1 < 3 / 20 then 1 else 49 / 50) * coefficient (B.lo 0) * lo

def weightUpper (B : Box) (hi : ℚ) : ℚ :=
  (if B.lo 1 < 3 / 20 then 1 else 49 / 50) * coefficient (B.hi 0) * hi

def weightMin (B : Box) (w : Witness) : ℚ := weightLower B (units w.σLower)

def weightMax (B : Box) (w : Witness) : ℚ := weightUpper B (units w.σUpper)

def nearLow (B : Box) (w : Witness) : ℚ :=
  min (aMin B * nearSlope B w) (aMax B * nearSlope B w)

def signedLow (B : Box) (w : Witness) : ℚ :=
  min (kMin B * core w) (kMax B * core w) -
    max (aMin B * farSlope B w) (aMax B * farSlope B w) -
    (units w.pairShift - units w.pairStart) / 2

def margin (B : Box) (w : Witness) (μ : ℚ) : ℚ :=
  (1 - μ) * nearLow B w + μ * signedLow B w

def BoxOK (B : Box) : Prop :=
  0 ≤ B.lo 0 ∧ 0 ≤ B.lo 1 ∧ B.hi 1 ≤ 1 / 5 ∧
  -1 ≤ B.lo 2 ∧ B.hi 2 ≤ 1 ∧ 0 < pathMax B

instance (B : Box) : Decidable (BoxOK B) := by unfold BoxOK; infer_instance

def witnessOK (B : Box) (w : Witness) : Bool :=
  decide (BoxOK B) &&
    G3Power.lower (1 + B.lo 2) (units w.left) &&
    G3Power.lower (1 - B.hi 2) (units w.right) &&
    G3Power.upper (1 + B.lo 2 - pathMax B) (units w.leftShift) &&
    G3Power.upper (1 - B.hi 2 - pathMax B) (units w.rightShift) &&
    G3Power.upper (B.hi 3 + pathMax B) (units w.farShift) &&
    G3Power.lower (B.hi 3) (units w.farStart) &&
    G3Power.upper (farBase B - 2) (units w.pairShift) &&
    G3Power.lower (farBase B) (units w.pairStart) &&
    G3Power.upper (rowAbsMax B) (units w.zPower) &&
    G3Power.crossLE (units w.σLower) (B.lo 1) 25 12 &&
    G3Power.crossLE (B.hi 1) (units w.σUpper) 12 25 &&
    decide (0 ≤ margin B w (weightMin B w)) &&
    decide (0 ≤ margin B w (weightMax B w))

inductive Tree where
  | cell (w : Witness)
  | cut (axis : Fin 4) (lower upper : Tree)

def midpoint (B : Box) (axis : Fin 4) : ℚ := (B.lo axis + B.hi axis) / 2

def Tree.ok (B : Box) : Tree → Bool
  | .cell w => witnessOK B w
  | .cut axis lower upper =>
    lower.ok (B.lowerChild axis (midpoint B axis)) &&
    upper.ok (B.upperChild axis (midpoint B axis))

end HlawkaSchatten.BelowExponent.G3S
