/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.SideConeCoarseRows

/-! Verify near-cone row bisections directly from their closed grid boundaries. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

structure SideConeRowSpan (n : Nat) where
  lo : Fin (n+1)
  hi : Fin (n+1)

def SideConeRowSpan.bounds (S : SideConeRowSpan n) (nodes : Vector ℚ (n+1)) : RatBounds :=
  ⟨nodes.get S.lo, nodes.get S.hi⟩

def SideConeRowSpan.covers (S : SideConeRowSpan n) (i : Fin n) : Prop :=
  S.lo.val ≤ i.val ∧ i.val < S.hi.val

def SideConeRowSpan.mid (S : SideConeRowSpan n) : Fin (n+1) :=
  ⟨(S.lo.val + S.hi.val) / 2, by
    have h := S.lo.isLt
    have h' := S.hi.isLt
    omega⟩

def SideConeRowSpan.first (S : SideConeRowSpan n) : SideConeRowSpan n := ⟨S.lo, S.mid⟩
def SideConeRowSpan.second (S : SideConeRowSpan n) : SideConeRowSpan n := ⟨S.mid, S.hi⟩

theorem SideConeRowSpan.split_cover {S : SideConeRowSpan n} {i : Fin n} (h : S.covers i) :
    S.first.covers i ∨ S.second.covers i := by
  rcases lt_or_ge i.val S.mid.val with hleft | hright
  · exact Or.inl ⟨h.1, hleft⟩
  · exact Or.inr ⟨hright, h.2⟩

theorem SideConeRowSpan.bounds_contains {S : SideConeRowSpan n} {nodes : Vector ℚ (n+1)}
    (hmono : ∀ i j : Fin (n+1), i.val ≤ j.val → nodes.get i ≤ nodes.get j)
    {i : Fin n} (hi : S.covers i) {x : ℝ} (hx : (sideRowInterval nodes i).Contains x) :
    (S.bounds nodes).Contains x := by
  have hlo := hmono S.lo i.castSucc hi.1
  have hhi := hmono i.succ S.hi hi.2
  exact ⟨(show ((S.bounds nodes).lo : ℝ) ≤ (sideRowInterval nodes i).lo by exact_mod_cast hlo).trans hx.1,
    hx.2.trans (show ((sideRowInterval nodes i).hi : ℝ) ≤ (S.bounds nodes).hi by exact_mod_cast hhi)⟩

def sideCoarseUStart (positive : Bool) : SideConeRowSpan 27 :=
  if positive then ⟨8,27⟩ else ⟨0,8⟩

def sideCoarseVStart (positive : Bool) : SideConeRowSpan 36 :=
  if positive then ⟨9,36⟩ else ⟨0,9⟩

inductive SideConeCoarseTree where
  | omitted
  | tile (T : SideCoarseTile)
  | cutU (left right : SideConeCoarseTree)
  | cutV (left right : SideConeCoarseTree)

def SideConeCoarseTree.checkWith (tileCheck : SideCoarseTile → Bool) :
    SideConeCoarseTree → SideConeRowSpan 27 → SideConeRowSpan 36 → Bool
  | .omitted, U, V => decide ((U.bounds sideUNodes).hi + (V.bounds sideVNodes).hi ≤ -5/8)
  | .tile T, U, V => (U.bounds sideUNodes).containedIn T.u.bounds &&
      (V.bounds sideVNodes).containedIn T.v.bounds && tileCheck T
  | .cutU l r, U, V => l.checkWith tileCheck U.first V && r.checkWith tileCheck U.second V
  | .cutV l r, U, V => l.checkWith tileCheck U V.first && r.checkWith tileCheck U V.second

noncomputable def SideConeCoarseTree.check (C : ParameterCell) (T : SideConeCoarseTree) :=
  T.checkWith (SideCoarseTile.check C)

private theorem sideUNodes_order : ∀ i j : Fin 28, i.val ≤ j.val → sideUNodes.get i ≤ sideUNodes.get j :=
  by decide +kernel

private theorem sideVNodes_order : ∀ i j : Fin 37, i.val ≤ j.val → sideVNodes.get i ≤ sideVNodes.get j :=
  by decide +kernel

theorem SideConeCoarseTree.soundWith {C : ParameterCell} {T : SideConeCoarseTree}
    {tileCheck : SideCoarseTile → Bool}
    (hTile : ∀ d, tileCheck d = true → SideConeOn C d.u.bounds d.v.bounds)
    {U : SideConeRowSpan 27} {V : SideConeRowSpan 36} (ht : T.checkWith tileCheck U V = true)
    {ij : Fin 27 × Fin 36} (hi : U.covers ij.1) (hj : V.covers ij.2) (hkeep : ij ∈ sideRowGrid) :
    SideConeOn C (sideURange ij.1) (sideVRange ij.2) := by
  induction T generalizing U V with
  | omitted =>
    have hcut : (-5/8 : ℚ) < (sideURange ij.1).hi + (sideVRange ij.2).hi :=
      of_decide_eq_true (List.mem_filter.mp hkeep).2
    have hmax : (U.bounds sideUNodes).hi + (V.bounds sideVNodes).hi ≤ -5/8 := of_decide_eq_true ht
    have hU : (sideURange ij.1).hi ≤ (U.bounds sideUNodes).hi :=
      sideUNodes_order ij.1.succ U.hi hi.2
    have hV : (sideVRange ij.2).hi ≤ (V.bounds sideVNodes).hi :=
      sideVNodes_order ij.2.succ V.hi hj.2
    exact False.elim ((not_lt_of_ge ((add_le_add hU hV).trans hmax)) hcut)
  | tile d =>
    simp only [SideConeCoarseTree.checkWith, Bool.and_eq_true, and_assoc] at ht
    obtain ⟨hU, hV, hc⟩ := ht
    intro a b η u v hp hu hv
    exact hTile d hc hp
      (RatBounds.containedIn_sound hU (U.bounds_contains sideUNodes_order hi hu))
      (RatBounds.containedIn_sound hV (V.bounds_contains sideVNodes_order hj hv))
  | cutU l r hl hr =>
    obtain ⟨hlt, hrt⟩ := Bool.and_eq_true_iff.mp ht
    rcases U.split_cover hi with hleft | hright
    · exact hl hlt hleft hj
    · exact hr hrt hright hj
  | cutV l r hl hr =>
    obtain ⟨hlt, hrt⟩ := Bool.and_eq_true_iff.mp ht
    rcases V.split_cover hj with hleft | hright
    · exact hl hlt hi hleft
    · exact hr hrt hi hright

theorem sideConeCoarseTrees_soundWith {C : ParameterCell} {trees : Bool → Bool → SideConeCoarseTree}
    {tileCheck : SideCoarseTile → Bool}
    (hTile : ∀ d, tileCheck d = true → SideConeOn C d.u.bounds d.v.bounds)
    (hc : ∀ s t, (trees s t).checkWith tileCheck (sideCoarseUStart s) (sideCoarseVStart t) = true) :
    ∀ ij ∈ sideRowGrid, SideConeOn C (sideURange ij.1) (sideVRange ij.2) := by
  intro ij hj
  have hu : ∃ s, (sideCoarseUStart s).covers ij.1 := by
    rcases lt_or_ge ij.1.val 8 with h | h
    · exact ⟨false, Nat.zero_le _, h⟩
    · exact ⟨true, h, ij.1.isLt⟩
  have hv : ∃ s, (sideCoarseVStart s).covers ij.2 := by
    rcases lt_or_ge ij.2.val 9 with h | h
    · exact ⟨false, Nat.zero_le _, h⟩
    · exact ⟨true, h, ij.2.isLt⟩
  obtain ⟨s, hs⟩ := hu
  obtain ⟨t, ht⟩ := hv
  exact SideConeCoarseTree.soundWith hTile (hc s t) hs ht hj

theorem sideConeCoarseTrees_sound {C : ParameterCell} {trees : Bool → Bool → SideConeCoarseTree}
    (hc : ∀ s t, (trees s t).check C (sideCoarseUStart s) (sideCoarseVStart t) = true) :
    ∀ ij ∈ sideRowGrid, SideConeOn C (sideURange ij.1) (sideVRange ij.2) :=
  sideConeCoarseTrees_soundWith (fun d h => d.tree.checkOn_sound d.u d.v C h) hc

end HlawkaSchatten.BelowExponent.Vertex
