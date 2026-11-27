/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import Init.Data.Int.Kernel

/-! Cross-power comparisons on unreduced fraction parts. -/

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3Power.Kernel

def crossNatLE (xn xd yn yd m n : Nat) : Bool :=
  Nat.ble
    (Nat.mul (Nat.pow xn m) (Nat.pow yd n))
    (Nat.mul (Nat.pow yn n) (Nat.pow xd m))

noncomputable def crossIntLE (xn : Int) (xd : Nat) (yn : Int) (yd m n : Nat) : Bool :=
  crossNatLE (Int.natAbs_k xn) xd (Int.natAbs_k yn) yd m n

noncomputable def absPartsLeOne (xn : Int) (xd : Nat) : Bool :=
  Nat.ble (Int.natAbs_k xn) xd

noncomputable def partsLeOne (xn : Int) (xd : Nat) : Bool :=
  Int.rec (fun n => Nat.ble n xd) (fun _ => true) xn

end HlawkaSchatten.BelowExponent.G3Power.Kernel
