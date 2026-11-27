/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public meta import HlawkaSchatten.BelowExponent.Vertex.CurvatureCheck
public meta import Lean
public meta import Mathlib.Tactic.FinCases

/-! Produce the intermediate radical jets for the kernel's two arithmetic checks. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

public meta section

namespace HlawkaSchatten.BelowExponent.Vertex

open Lean Elab Tactic Meta

private def intTerm (n : ℤ) : TacticM Term := do
  let value := Syntax.mkNumLit (toString n.natAbs)
  if n < 0 then `(term| -$value:num) else `(term| $value:num)

private def boundsTerm (b : DyadicBounds) : TacticM Term := do
  let lo ← intTerm b.lo
  let hi ← intTerm b.hi
  let ok ← if b.ok then `(term| true) else `(term| false)
  `(term| ⟨$lo, $hi, $ok⟩)

private def jetTerm (j : IntervalJet) : TacticM Term := do
  let v ← boundsTerm j.value
  let d ← boundsTerm j.first
  let dd ← boundsTerm j.second
  `(term| ⟨$v, $d, $dd⟩)

private def vectorTerm {α : Type} (quoteValue : α → TacticM Term) (row : Vector α 3) : TacticM Term := do
  let a ← quoteValue (row.get 0)
  let b ← quoteValue (row.get 1)
  let c ← quoteValue (row.get 2)
  `(term| #v[$a, $b, $c])

/-- The computed table is a witness. Both the table and its consequences are reduced in the kernel. -/
syntax (name := replayCurvatureSubcell) "replay_curvature_subcell" : tactic

@[tactic replayCurvatureSubcell]
unsafe def elabReplayCurvatureSubcell : Tactic := fun _ => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOfArity ``Eq 3 do
    throwError "expected an equality for subcellCurvatureOK"
  let lhs := target.appFn!.appArg!
  unless lhs.isAppOfArity ``subcellCurvatureOK 4 && target.appArg!.isConstOf ``Bool.true do
    throwError "expected subcellCurvatureOK to equal true"
  let args := lhs.getAppArgs
  let value := mkApp2 (mkConst ``radicalIntervalTable) args[0]! args[1]!
  let vector3 (type : Expr) := mkApp2 (mkConst ``Vector [Level.zero]) type (mkRawNatLit 3)
  let table ← evalExpr (Vector (Vector IntervalJet 3) 3) (vector3 (vector3 (mkConst ``IntervalJet))) value
  let literal ← vectorTerm (vectorTerm jetTerm) table
  evalTactic (← `(tactic| refine subcellCurvatureOK_of_radical_table (table := $literal) ?_ ?_ <;> decide +kernel))

macro "replay_curvature_layer" : tactic => `(tactic|
  (apply gridLayerCurvatureOK_of_cells
   intro j k
   fin_cases j <;> fin_cases k <;> replay_curvature_subcell))

end HlawkaSchatten.BelowExponent.Vertex
