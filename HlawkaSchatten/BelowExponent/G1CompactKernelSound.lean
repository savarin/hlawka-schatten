/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1CompactKernelData

/-! The native compact G1 checks equal their original integer checks. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G1CompactData

open Vertex

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem lowerOrdinateKernel_knots : ∀ node : Fin 129,
    lowerOrdinateKernel (knotNum node).natAbs =
      lowerOrdinates[(knotNum node).natAbs]?.getD 0 := by
  decide +kernel

theorem lowerOrdinateKernel_default {n : Nat} (h : 65 ≤ n) : lowerOrdinateKernel n = 0 := by
  have hb : Nat.ble n 64 = false := by
    cases he : Nat.ble n 64 with
    | false => rfl
    | true =>
      have hc : n ≤ 64 := by simpa only [Nat.ble_eq] using he
      omega
  simp only [lowerOrdinateKernel, hb, Bool.cond_false]

theorem intCoefficientsKernel_eq (P : G1CompactParams) :
    intCoefficientsKernel P = intCoefficients P := by
  simp only [intCoefficientsKernel, intCoefficients, Int.mul_k_eq, Int.ofNat_eq_natCast]
  rfl

theorem intCornerKernel_eq (l : Nat) (coeff : IntegerCoefficients) (node : Fin 129) :
    intCornerKernel l coeff node = intCorner l coeff node := by
  simp only [intCornerKernel, Int.mul_k_eq, Int.add_k_eq, Int.sub_k_eq,
    Int.ofNat_eq_natCast, intNonnegK_eq, lowerOrdinateKernel_knots, intCorner, pow_two]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  change _ - _ ≥ 0 ↔ _ ≤ _
  exact sub_nonneg

theorem overlapsCompactKernel_eq (l w : Nat) (node : Fin 128) :
    overlapsCompactKernel l w node = decide (overlapsCompact l w node) := by
  simp only [overlapsCompactKernel, Int.mul_k_eq, Int.add_k_eq, Int.sub_k_eq,
    Int.ofNat_eq_natCast, intNonnegK_eq, overlapsCompact]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  change (0 ≤ ((4096 - (l : ℤ)) * knotNum node.succ + 256 * l) + 64 * w ∧
      0 ≤ 64 * w - ((4096 - (l : ℤ)) * knotNum node.castSucc + 256 * l)) ↔ _
  constructor
  · intro h
    constructor <;> omega
  · intro h
    constructor <;> omega

theorem intBoxKernel_eq (l w : Nat) (coeff : IntegerCoefficients) (node : Fin 128) :
    intBoxKernel l w coeff node = intBox l w coeff node := by
  simp only [intBoxKernel, intBox, overlapsCompactKernel_eq, intCornerKernel_eq]

theorem intBinKernel_eq (i : Fin 13) (right : Bool) (j : Fin 64) :
    intBinKernel i right j = intBin i right j := by
  unfold intBinKernel intBin
  rw [intCoefficientsKernel_eq]
  congr 1
  funext node
  exact intBoxKernel_eq _ _ _ node

theorem intSideBlockKernel_eq (i : Fin 13) (right : Bool) (block : Fin 16) :
    intSideBlockKernel i right block = intSideBlock i right block := by
  simp only [intSideBlockKernel, intSideBlock, intBinKernel_eq]

theorem intSideBlock_of_kernel {i : Fin 13} {right : Bool} {block : Fin 16}
    (h : intSideBlockKernel i right block = true) : intSideBlock i right block = true := by
  rw [← intSideBlockKernel_eq]
  exact h

end HlawkaSchatten.BelowExponent.G1CompactData
