/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeCoarseTree

/-! Join independently checked subtrees along their original closed row cuts. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

theorem SideConeCoarseTree.cutU_checked {C : ParameterCell} {l r : SideConeCoarseTree}
    {U : SideConeRowSpan 27} {V : SideConeRowSpan 36}
    (hl : l.check C U.first V = true) (hr : r.check C U.second V = true) :
    (SideConeCoarseTree.cutU l r).check C U V = true :=
  Bool.and_eq_true_iff.mpr ⟨hl, hr⟩

theorem SideConeCoarseTree.cutV_checked {C : ParameterCell} {l r : SideConeCoarseTree}
    {U : SideConeRowSpan 27} {V : SideConeRowSpan 36}
    (hl : l.check C U V.first = true) (hr : r.check C U V.second = true) :
    (SideConeCoarseTree.cutV l r).check C U V = true :=
  Bool.and_eq_true_iff.mpr ⟨hl, hr⟩

end HlawkaSchatten.BelowExponent.Vertex
