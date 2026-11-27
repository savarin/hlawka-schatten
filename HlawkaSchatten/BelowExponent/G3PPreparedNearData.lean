/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PCommonKernelData

/-! A shared-input entry point for the exact raw near polynomial. -/

set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

noncomputable section

structure PreparedNear where
  H : CommonDen
  U : CommonDen
  K : CommonDen
  W : CommonDen
  M : CommonDen
  jensen : RawScalar

def RawScalar.point (a : RawScalar) : CommonDen := ⟨a.num, a.num, a.den, a.den_pos⟩

def PreparedNear.fromBox (B : Box) (w : RowWitness) : PreparedNear :=
  let K := CommonDen.Kernel.ofBounds (kBounds B)
  let W := CommonDen.Kernel.mul K (CommonDen.Kernel.sub
    (CommonDen.Kernel.ofBounds (bounds B 3)) (CommonDen.ofRat 1))
  ⟨CommonDen.Kernel.ofBounds (bounds B 0), CommonDen.Kernel.ofBounds (bounds B 2),
    K, W, CommonDen.Kernel.ofBounds (muBounds B w), RawScalar.ofRat (w.jensen.value B)⟩

def nearRawPrepared (positive : Bool) (x : PreparedNear) : RawLowerPolynomial :=
  let P := CommonDen.ofRat
  let mul := CommonDen.Kernel.mul
  let add := CommonDen.Kernel.add
  let sub := CommonDen.Kernel.sub
  let even := CommonDen.Kernel.evenPow
  let H := x.H
  let U := x.U
  let K := x.K
  let S := mul (P (signRat positive)) U
  let W := x.W
  let h2 := sub (P 2) H
  let h1 := sub (P 1) H
  let V := add (mul h1 S) (mul H W)
  let M := x.M
  let b := sub (P 1) M
  let mk := mul M K
  let u2 := even U 2
  let w2 := even W 2
  let cross2 := mul (mul (mul (P 2) h1) W) S
  let d2 := sub (sub (mul h2 u2) cross2) (mul H w2)
  let gain := mul (CommonDen.Kernel.ofBounds c4)
    (add (mul (mul b d2) (add u2 (even V 2))) (mul mk (even U 4)))
  let C := CommonDen.Kernel.ofBounds c2
  ⟨RawScalar.lower (mul C (add (mul b h2) mk)),
    RawScalar.upper (mul (mul (mul (mul b C) (P 2)) h1) (mul W (P (signRat positive)))),
    RawScalar.sub
      (RawScalar.sub (RawScalar.lower (add (mul mk (RawScalar.point x.jensen)) gain))
        (RawScalar.upper (mul (mul (mul b C) H) w2)))
      (tailRaw b W U)⟩

end

end HlawkaSchatten.BelowExponent.G3P
