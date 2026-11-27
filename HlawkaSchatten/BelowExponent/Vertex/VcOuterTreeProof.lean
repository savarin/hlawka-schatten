/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.VcOuterTreeCheck
public import HlawkaSchatten.BelowExponent.Vertex.SideOuterWideProof

/-! A checked VC tree family discharges the shared real margin at one parameter point. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

theorem vcOuterValid_of_treesOK {p : SideCornerEntry} {P : OuterPointBounds}
    {roots : Fin 3 → RatBounds} {trees : Vector SideOuterTree 12}
    (hr : p.cell.rootsOK roots = true) (hp : P = .atPoint p.a p.b p.eta p.margin roots)
    (hc : vcOuterTreesOK P trees = true) : p.ValidFor (fun _ => True) := by
  apply vcOuterPoint_of_checked_trees (trees := fun k s t => trees.get (outerTreeIndex k s t)) hr hp
  intro k s t
  have member (v : Bool) : v ∈ [false,true] := by cases v <;> simp
  exact List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hc k (List.mem_finRange k))
    s (member s)) t (member t)

end HlawkaSchatten.BelowExponent.Vertex
