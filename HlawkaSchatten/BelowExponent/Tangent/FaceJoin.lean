/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.Checker

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.TC

/-- Join the three checked faces without recomputing any face in the kernel. -/
theorem cellOK_of_faces (H : Hdr) (G : Geom) (p₀ p₁ p₂ p₃ g₀ g₁ g₂ f₁ f₂ f₃ : Nat)
    (hw : (Nat.blt 0 H.Dw && p₀ + p₁ + p₂ + p₃ == H.Dw &&
      Nat.ble (g₀ + g₁ + g₂) H.Dw && geomOK G) = true)
    (h₁ : faceOK (mkCtx H) (mkFace (mkCtx H) (cellVerts G).1 (cellVerts G).2
      [p₀, p₁, p₂, p₃] [g₀, g₁, g₂] 0 1 2) H.KBOX f₁ = true)
    (h₂ : faceOK (mkCtx H) (mkFace (mkCtx H) (cellVerts G).1 (cellVerts G).2
      [p₀, p₁, p₂, p₃] [g₀, g₁, g₂] 1 0 2) H.KBOX f₂ = true)
    (h₃ : faceOK (mkCtx H) (mkFace (mkCtx H) (cellVerts G).1 (cellVerts G).2
      [p₀, p₁, p₂, p₃] [g₀, g₁, g₂] 2 0 1) H.KBOX f₃ = true) :
    cellOK H G ⟨[p₀, p₁, p₂, p₃], [g₀, g₁, g₂], f₁, f₂, f₃⟩ = true := by
  cases h : cellVerts G with
  | mk V D =>
    simp only [h] at h₁ h₂ h₃
    simp only [cellOK, h, h₁, h₂, h₃, Bool.and_true, hw]

end HlawkaSchatten.BelowExponent.TC
