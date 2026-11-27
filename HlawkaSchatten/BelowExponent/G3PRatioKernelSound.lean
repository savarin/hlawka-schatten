/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PRatioKernelData
public import HlawkaSchatten.BelowExponent.G3PCommonKernelSound

/-! All-input transport from the native ratio checker to the original checker. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

noncomputable section

open Vertex (RatBounds)

theorem TiledRow.quadRaw_ok_eq (w : TiledRow) (B : Box) (b : Bool) :
    (w.quadRaw B b).ok = (w.quad B b).ok := by
  simp only [TiledRow.quadRaw, RawLowerPolynomial.quad_ok_eq,
    RawScalar.value_mul, RawScalar.value_sub, RawScalar.value_ofRat,
    nearTermsRaw_value_eq, nearTermsKernel_eq, sub_zero, TiledRow.quad]

theorem TiledRow.kernelOKOnRatio_eq (w : TiledRow) (B : Box) (b : Bool) (A : RatBounds) :
    w.kernelOKOnRatio B b A = w.okOnRatio B b A := by
  simp only [TiledRow.kernelOKOnRatio, TiledRow.okOnRatio, Quad.kernelOK_eq,
    TiledRow.quadRaw_ok_eq, G3Power.Kernel.crossIntLE_rat_eq]

theorem RatioChart.kernelOK_eq (t : RatioChart) (B : Box) (b : Bool) :
    t.kernelOK B b = t.ok B b := by
  induction t generalizing B with
  | original t => simp only [kernelOK, ok, CertTree.kernelOK_eq]
  | row w => simp only [kernelOK, ok, TiledRow.kernelOKOnRatio_eq]
  | cut j m l r hl hr => simp only [kernelOK, ok, hl, hr]

theorem RatioRemainder.kernelOK_eq (t : RatioRemainder) (B : Box) (b : Bool) (cap : ℚ) :
    t.kernelOK B b cap = t.ok B b cap := by
  induction t generalizing B with
  | original t => exact CertTree.kernelOK_eq t B b
  | covered => rfl
  | cut j m l r hl hr => simp only [kernelOK, ok, hl, hr]

theorem RatioChart.ok_of_kernelOK {t : RatioChart} {B : Box} {b : Bool}
    (h : t.kernelOK B b = true) : t.ok B b = true :=
  (t.kernelOK_eq B b).symm.trans h

theorem RatioRemainder.ok_of_kernelOK {t : RatioRemainder} {B : Box} {b : Bool} {cap : ℚ}
    (h : t.kernelOK B b cap = true) : t.ok B b cap = true :=
  (t.kernelOK_eq B b cap).symm.trans h

end

end HlawkaSchatten.BelowExponent.G3P
