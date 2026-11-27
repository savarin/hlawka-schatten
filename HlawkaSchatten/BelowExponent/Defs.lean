/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.VecNotation

/-! The scalar row condition of Route T, in the order of the four sign vectors
`(+,+,+)`, `(-,-,+)`, `(-,+,-)`, `(+,-,-)`. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

abbrev Profile := Fin 4 → ℝ
abbrev Row := Fin 3 → ℝ

def partner (j : Fin 3) (s : Fin 4) : Fin 4 :=
  ![![3, 2, 1, 0], ![2, 3, 0, 1], ![1, 0, 3, 2]] j s

def sign (j : Fin 3) (s : Fin 4) : ℝ :=
  if s = 0 ∨ s = partner j 0 then 1 else -1

def rowEval (t : Profile) (s : Fin 4) (x : Row) : ℝ :=
  ∑ j, sign j s * (t s + t (partner j s)) * x j

def IsSimplex (t : Profile) : Prop :=
  (∀ s, 0 ≤ t s) ∧ ∑ s, t s = 1

def WeightedRow (q : ℝ) (t π : Profile) (γ x : Row) : Prop :=
  ∑ s, π s * |rowEval t s x| ^ q ≤ ∑ j, γ j * |x j| ^ q

def RowAt (q : ℝ) (t : Profile) : Prop :=
  ∃ π : Profile, IsSimplex π ∧ ∃ γ : Row,
    (∀ j, 0 ≤ γ j) ∧ (∑ j, γ j) ≤ 1 ∧ ∀ x, WeightedRow q t π γ x

end HlawkaSchatten.BelowExponent
