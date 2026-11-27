/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeFastRows

/-! Closed bisections and a shared parameter table for bounded SC replay batches. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def RatBounds.sideHalf (I : RatBounds) (upper : Bool) : RatBounds :=
  let m := (I.lo + I.hi)/2
  if upper then ⟨m,I.hi⟩ else ⟨I.lo,m⟩

theorem RatBounds.sideHalf_cover {I : RatBounds} {x : ℝ} (hx : I.Contains x) :
    (I.sideHalf false).Contains x ∨ (I.sideHalf true).Contains x := by
  rcases le_total x (((I.lo+I.hi)/2 : ℚ) : ℝ) with h | h
  · exact Or.inl ⟨hx.1,h⟩
  · exact Or.inr ⟨h,hx.2⟩

def ParameterCell.sideHalf (C : ParameterCell) (axis : Fin 3) (upper : Bool) : ParameterCell :=
  if axis = 0 then { C with a := C.a.sideHalf upper }
  else if axis = 1 then { C with b := C.b.sideHalf upper }
  else { C with η := C.η.sideHalf upper }

theorem ParameterCell.sideHalf_cover {C : ParameterCell} {a b η : ℝ} (h : C.Contains a b η)
    (axis : Fin 3) : (C.sideHalf axis false).Contains a b η ∨ (C.sideHalf axis true).Contains a b η := by
  fin_cases axis
  · rcases RatBounds.sideHalf_cover h.first with hl | hr
    · exact Or.inl ⟨hl,h.second,h.eta⟩
    · exact Or.inr ⟨hr,h.second,h.eta⟩
  · rcases RatBounds.sideHalf_cover h.second with hl | hr
    · exact Or.inl ⟨h.first,hl,h.eta⟩
    · exact Or.inr ⟨h.first,hr,h.eta⟩
  · rcases RatBounds.sideHalf_cover h.eta with hl | hr
    · exact Or.inl ⟨h.first,h.second,hl⟩
    · exact Or.inr ⟨h.first,h.second,hr⟩

def RatBounds.containedIn (I J : RatBounds) : Bool := decide (J.lo ≤ I.lo ∧ I.hi ≤ J.hi)

theorem RatBounds.containedIn_sound {I J : RatBounds} (h : I.containedIn J = true) {x : ℝ}
    (hx : I.Contains x) : J.Contains x := by
  have hs := of_decide_eq_true h
  exact ⟨(by exact_mod_cast hs.1 : (J.lo : ℝ) ≤ I.lo).trans hx.1,
    hx.2.trans (by exact_mod_cast hs.2 : (I.hi : ℝ) ≤ J.hi)⟩

def ParameterCell.containedIn (C D : ParameterCell) : Bool :=
  C.a.containedIn D.a && C.b.containedIn D.b && C.η.containedIn D.η

theorem ParameterCell.containedIn_sound {C D : ParameterCell} (h : C.containedIn D = true) {a b η : ℝ}
    (hp : C.Contains a b η) : D.Contains a b η := by
  simp only [ParameterCell.containedIn, Bool.and_eq_true, and_assoc] at h
  exact ⟨RatBounds.containedIn_sound h.1 hp.first, RatBounds.containedIn_sound h.2.1 hp.second,
    RatBounds.containedIn_sound h.2.2 hp.eta⟩

structure SideFastGrid where
  u : Fin 27 → SideFastAxis
  v : Fin 36 → SideFastAxis

def SideFastGrid.check (G : SideFastGrid) : Bool :=
  (List.finRange 27).all (fun i => (G.u i).check (sideURange i)) &&
    (List.finRange 36).all (fun j => (G.v j).check (sideVRange j))

inductive SideFastTree where
  | leaf (index : Nat) (mixed : FactorSamples)
  | bisect (axis : Fin 3) (lo hi : SideFastTree)

def SideFastTree.check (G : SideFastGrid) (table : Array SideFastParameter)
    (row : Fin 27 × Fin 36) (C : ParameterCell) : SideFastTree → Bool
  | .leaf i M =>
    match table[i]? with
    | none => false
    | some P => C.containedIn P.cell &&
        P.leafCheck (sideURange row.1) (sideVRange row.2) (G.u row.1) (G.v row.2) M
  | .bisect axis l r => check G table row (C.sideHalf axis false) l &&
      check G table row (C.sideHalf axis true) r

theorem SideFastTree.check_sound {G : SideFastGrid} {table : Array SideFastParameter}
    (hG : G.check = true)
    (hP : ∀ (i : ℕ) (P : SideFastParameter), table[i]? = some P → P.check = true)
    (row : Fin 27 × Fin 36) (C : ParameterCell) (T : SideFastTree)
    (hT : T.check G table row C = true) : SideConeOn C (sideURange row.1) (sideVRange row.2) := by
  induction T generalizing C with
  | leaf i M =>
    cases hi : table[i]? with
    | none => simp [SideFastTree.check, hi] at hT
    | some P =>
      simp only [SideFastTree.check, hi, Bool.and_eq_true] at hT
      have hb := Bool.and_eq_true_iff.mp hG
      have hU := List.all_eq_true.mp hb.1 row.1 (by simp)
      have hV := List.all_eq_true.mp hb.2 row.2 (by simp)
      have h := SideFastParameter.leafCheck_sound (hP i P hi) hU hV hT.2
      intro a b η u v hc hu hv
      exact h (ParameterCell.containedIn_sound hT.1 hc) hu hv
  | bisect axis l r il ir =>
    simp only [SideFastTree.check, Bool.and_eq_true] at hT
    intro a b η u v hc hu hv
    rcases ParameterCell.sideHalf_cover hc axis with hl | hr
    · exact il _ hT.1 hl hu hv
    · exact ir _ hT.2 hr hu hv

theorem sideFastTable_sound {table : Array SideFastParameter}
    (h : table.toList.all SideFastParameter.check = true) :
    ∀ (i : ℕ) (P : SideFastParameter), table[i]? = some P → P.check = true := by
  intro i P hi
  apply List.all_eq_true.mp h
  exact Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨i, hi⟩)

structure SideFastRowTree where
  row : Fin 27 × Fin 36
  tree : SideFastTree

def SideFastRowTree.check (G : SideFastGrid) (table : Array SideFastParameter)
    (C : ParameterCell) (R : SideFastRowTree) : Bool := R.tree.check G table R.row C

theorem sideFastRows_sound {G : SideFastGrid} {table : Array SideFastParameter} {C : ParameterCell}
    {data : List SideFastRowTree} (hG : G.check = true) (hP : table.toList.all SideFastParameter.check = true)
    (ht : data.all (SideFastRowTree.check G table C) = true)
    (hcover : data.map SideFastRowTree.row = sideRowGrid) :
    ∀ row ∈ sideRowGrid, SideConeOn C (sideURange row.1) (sideVRange row.2) := by
  intro row hr
  rw [← hcover] at hr
  obtain ⟨R, hmem, hrow⟩ := List.mem_map.mp hr
  subst row
  exact R.tree.check_sound hG (sideFastTable_sound hP) R.row C (List.all_eq_true.mp ht R hmem)

end HlawkaSchatten.BelowExponent.Vertex
