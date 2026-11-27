/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G3PPreparedNearData
public import HlawkaSchatten.BelowExponent.G3PCommonKernelSound

/-! Exact matching conditions for shared raw near-polynomial inputs. -/

set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G3P

theorem nearRawPrepared_fromBox (B : Box) (positive : Bool) (w : RowWitness) :
    nearRawPrepared positive (PreparedNear.fromBox B w) = nearTermsRaw B positive w := by
  rfl

theorem nearRawPrepared_eq_of_fields (B : Box) (positive : Bool) (w : RowWitness)
    (x : PreparedNear)
    (hH : x.H = CommonDen.Kernel.ofBounds (bounds B 0))
    (hU : x.U = CommonDen.Kernel.ofBounds (bounds B 2))
    (hK : x.K = CommonDen.Kernel.ofBounds (kBounds B))
    (hW : x.W = CommonDen.Kernel.mul (CommonDen.Kernel.ofBounds (kBounds B))
      (CommonDen.Kernel.sub (CommonDen.Kernel.ofBounds (bounds B 3)) (CommonDen.ofRat 1)))
    (hM : x.M = CommonDen.Kernel.ofBounds (muBounds B w))
    (hJ : x.jensen = RawScalar.ofRat (w.jensen.value B)) :
    nearRawPrepared positive x = nearTermsRaw B positive w := by
  have hx : x = PreparedNear.fromBox B w := by
    cases x
    cases hH
    cases hU
    cases hK
    cases hW
    cases hM
    cases hJ
    rfl
  rw [hx, nearRawPrepared_fromBox]

theorem nearRawPrepared_value (B : Box) (positive : Bool) (w : RowWitness) :
    (nearRawPrepared positive (PreparedNear.fromBox B w)).value = nearTermsCommon B positive w := by
  rw [nearRawPrepared_fromBox, nearTermsRaw_value_eq, nearTermsKernel_eq]

end HlawkaSchatten.BelowExponent.G3P
