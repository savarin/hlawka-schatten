/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.Checker

/-! Join checks of packed subtrees while preserving the exact suffix after each subtree. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

namespace HlawkaSchatten.BelowExponent.TC

def walkBox (C : Ctx) (F : Face) (fuel stream a₀ a₁ b₀ b₁ : Nat) : Bool × Nat :=
  walk C F fuel stream a₀ a₁ b₀ b₁ (lmaxAt C F a₀ b₀) (lmaxAt C F a₀ b₁)
    (lmaxAt C F a₁ b₀) (lmaxAt C F a₁ b₁)

theorem walkBox_splitA {C : Ctx} {F : Face} {fuel stream a₀ a₁ b₀ b₁ suffix rest : Nat}
    (tag : stream % 4 = 0)
    (left : walkBox C F fuel (stream >>> 2) a₀ ((a₀ + a₁) / 2) b₀ b₁ = (true, suffix))
    (right : walkBox C F fuel suffix ((a₀ + a₁) / 2) a₁ b₀ b₁ = (true, rest)) :
    walkBox C F (fuel + 1) stream a₀ a₁ b₀ b₁ = (true, rest) := by
  unfold walkBox at *
  simp only [walk, tag, ↓reduceIte, left, right]

theorem walkBox_splitB {C : Ctx} {F : Face} {fuel stream a₀ a₁ b₀ b₁ suffix rest : Nat}
    (tag : stream % 4 = 1)
    (left : walkBox C F fuel (stream >>> 2) a₀ a₁ b₀ ((b₀ + b₁) / 2) = (true, suffix))
    (right : walkBox C F fuel suffix a₀ a₁ ((b₀ + b₁) / 2) b₁ = (true, rest)) :
    walkBox C F (fuel + 1) stream a₀ a₁ b₀ b₁ = (true, rest) := by
  unfold walkBox at *
  simp only [walk, tag, Nat.one_ne_zero, ↓reduceIte, left, right]

theorem faceOK_of_walkBox {C : Ctx} {F : Face} {KBOX stream : Nat}
    (h : walkBox C F (2 * KBOX + 4) stream 0 (2 * C.Da) 0 (2 * C.Da) = (true, 1)) :
    faceOK C F KBOX stream = true := by
  unfold walkBox at h
  simp [faceOK, h]

end HlawkaSchatten.BelowExponent.TC
