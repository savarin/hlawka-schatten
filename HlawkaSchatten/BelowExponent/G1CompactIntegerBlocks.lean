/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1CompactIntegerSound

/-! Check four consecutive imbalance bins at a time. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.G1CompactData

def compactBlockBin (block : Fin 16) (offset : Fin 4) : Fin 64 :=
  ⟨4 * block.val + offset.val, by
    have hb := block.isLt
    have ho := offset.isLt
    omega⟩

def intSideBlock (i : Fin 13) (right : Bool) (block : Fin 16) : Bool :=
  (List.finRange 4).all fun offset => intBin i right (compactBlockBin block offset)

private theorem intSide_of_blocks {i : Fin 13} {right : Bool}
    (h : ∀ block, intSideBlock i right block = true) : intSide i right = true := by
  apply List.all_eq_true.mpr
  intro j _
  let block : Fin 16 := ⟨j.val / 4, by have hj := j.isLt; omega⟩
  let offset : Fin 4 := ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩
  have hj : compactBlockBin block offset = j := Fin.ext (Nat.div_add_mod j.val 4)
  have hbin := List.all_eq_true.mp (h block) offset (List.mem_finRange offset)
  exact hj ▸ hbin

theorem compactCorners_of_blocks {i : Fin 13}
    (h : ∀ right block, intSideBlock i right block = true) :
    ∀ right j, compactCornersOK i right j :=
  intSlab_sound i (Bool.and_eq_true_iff.mpr ⟨intSide_of_blocks (h false), intSide_of_blocks (h true)⟩)

end HlawkaSchatten.BelowExponent.G1CompactData
