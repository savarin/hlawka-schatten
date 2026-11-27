/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.G1CompactKernelSound
meta import Mathlib.Tactic.FinCases

/-! Exact corner comparisons for compact G1 slab 9, four bins per check. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public section

namespace HlawkaSchatten.BelowExponent

open G1CompactData

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem leftBlock00 : intSideBlock 9 false 0 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock01 : intSideBlock 9 false 1 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock02 : intSideBlock 9 false 2 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock03 : intSideBlock 9 false 3 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock04 : intSideBlock 9 false 4 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock05 : intSideBlock 9 false 5 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock06 : intSideBlock 9 false 6 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock07 : intSideBlock 9 false 7 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock08 : intSideBlock 9 false 8 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock09 : intSideBlock 9 false 9 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock10 : intSideBlock 9 false 10 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock11 : intSideBlock 9 false 11 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock12 : intSideBlock 9 false 12 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock13 : intSideBlock 9 false 13 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock14 : intSideBlock 9 false 14 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlock15 : intSideBlock 9 false 15 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem leftBlocks (block : Fin 16) : intSideBlock 9 false block = true := by
  fin_cases block
  · exact leftBlock00
  · exact leftBlock01
  · exact leftBlock02
  · exact leftBlock03
  · exact leftBlock04
  · exact leftBlock05
  · exact leftBlock06
  · exact leftBlock07
  · exact leftBlock08
  · exact leftBlock09
  · exact leftBlock10
  · exact leftBlock11
  · exact leftBlock12
  · exact leftBlock13
  · exact leftBlock14
  · exact leftBlock15

private theorem rightBlock00 : intSideBlock 9 true 0 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock01 : intSideBlock 9 true 1 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock02 : intSideBlock 9 true 2 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock03 : intSideBlock 9 true 3 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock04 : intSideBlock 9 true 4 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock05 : intSideBlock 9 true 5 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock06 : intSideBlock 9 true 6 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock07 : intSideBlock 9 true 7 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock08 : intSideBlock 9 true 8 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock09 : intSideBlock 9 true 9 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock10 : intSideBlock 9 true 10 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock11 : intSideBlock 9 true 11 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock12 : intSideBlock 9 true 12 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock13 : intSideBlock 9 true 13 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock14 : intSideBlock 9 true 14 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlock15 : intSideBlock 9 true 15 = true := by
  apply intSideBlock_of_kernel
  decide +kernel

private theorem rightBlocks (block : Fin 16) : intSideBlock 9 true block = true := by
  fin_cases block
  · exact rightBlock00
  · exact rightBlock01
  · exact rightBlock02
  · exact rightBlock03
  · exact rightBlock04
  · exact rightBlock05
  · exact rightBlock06
  · exact rightBlock07
  · exact rightBlock08
  · exact rightBlock09
  · exact rightBlock10
  · exact rightBlock11
  · exact rightBlock12
  · exact rightBlock13
  · exact rightBlock14
  · exact rightBlock15

theorem compactCornerChecks09 : ∀ right j, compactCornersOK 9 right j := by
  apply compactCorners_of_blocks (i := 9)
  intro right
  cases right
  · exact leftBlocks
  · exact rightBlocks

end HlawkaSchatten.BelowExponent
