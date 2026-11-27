/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.CornerGridData
public import HlawkaSchatten.BelowExponent.Vertex.CornerPointData
public import HlawkaSchatten.BelowExponent.Vertex.CurvatureCertificates
public import HlawkaSchatten.BelowExponent.Vertex.SideConeJoin

/-! Match shared SC corner proofs to the exact points and margin budgets of the curvature grid. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

def SideCornerEntry.ValidFor (p : SideCornerEntry) (applies : Row → Prop) : Prop :=
  ∀ z, applies z → CornerMarginAt p.margin.get z p.a p.b p.eta

abbrev SideCornerEntry.Valid (p : SideCornerEntry) : Prop :=
  p.ValidFor fun z => ¬ InSideNearCone z

def SideCornerEntry.fits (p : SideCornerEntry) (cert : CurvatureCellCertificate) (i j k : Bool) :
    Bool :=
  decide (p.a = outerEndpoint cert.cell.a i ∧
    p.b = outerEndpoint cert.cell.b j ∧
    p.eta = outerEndpoint cert.cell.η k ∧
    ∀ m : Fin 3, cert.margins m ≤ p.margin.get m)

private theorem cast_outerEndpoint (r : RatBounds) (i : Bool) :
    (outerEndpoint r i : ℝ) = chooseCorner i (r.lo : ℝ) (r.hi : ℝ) := by
  cases i <;> rfl

theorem SideCornerEntry.fits_sound {p : SideCornerEntry} {cert : CurvatureCellCertificate}
    {i j k : Bool} {z : Row} {applies : Row → Prop} (hfit : p.fits cert i j k = true)
    (hp : p.ValidFor applies) (hz : applies z) : CornerMarginAt cert.margins z
      (chooseCorner i (cert.cell.lower 0) (cert.cell.upper 0))
      (chooseCorner j (cert.cell.lower 1) (cert.cell.upper 1))
      (chooseCorner k (cert.cell.lower 2) (cert.cell.upper 2)) := by
  obtain ⟨ha, hb, he, hm⟩ := of_decide_eq_true hfit
  have h := (hp z hz).mono hm
  rw [ha, hb, he, cast_outerEndpoint, cast_outerEndpoint, cast_outerEndpoint] at h
  exact h

def sideCornerIndex (i j k : Bool) : Fin 8 :=
  ⟨4 * i.toNat + 2 * j.toNat + k.toNat, by cases i <;> cases j <;> cases k <;> decide⟩

def sideCornerLinksLookupOK (lookup : Nat → Option SideCornerEntry) (cert : CurvatureCellCertificate)
    (links : Vector Nat 8) : Bool :=
  [false,true].all fun i => [false,true].all fun j => [false,true].all fun k =>
    match lookup (links.get (sideCornerIndex i j k)) with
    | some point => point.fits cert i j k
    | none => false

theorem sideCornerLinksLookup_sound {lookup : Nat → Option SideCornerEntry}
    {cert : CurvatureCellCertificate} {links : Vector Nat 8} {applies : Row → Prop}
    (hlinks : sideCornerLinksLookupOK lookup cert links = true)
    (hpoints : ∀ n p, lookup n = some p → p.ValidFor applies) {z : Row} (hz : applies z) :
    CellCornerMargins cert.cell cert.margins z := by
  intro i j k
  have hm (a : Bool) : a ∈ [false,true] := by cases a <;> decide
  have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hlinks i (hm i)) j (hm j)) k (hm k)
  let n := links.get (sideCornerIndex i j k)
  change (match lookup n with | some p => p.fits cert i j k | none => false) = true at h
  cases he : lookup n with
  | none => simp [he] at h
  | some p => exact SideCornerEntry.fits_sound (by simpa only [he] using h) (hpoints n p he) hz

def sideCornerGridLookupOK (lookup : Nat → Option SideCornerEntry) (certs : List CurvatureCellCertificate)
    (links : List (Vector Nat 8)) : Bool :=
  decide (certs.length = links.length) &&
    (certs.zip links).all fun (c, l) => sideCornerLinksLookupOK lookup c l

theorem sideCornerGridLookup_sound {lookup : Nat → Option SideCornerEntry}
    {certs : List CurvatureCellCertificate} {links : List (Vector Nat 8)} {applies : Row → Prop}
    (hgrid : sideCornerGridLookupOK lookup certs links = true)
    (hpoints : ∀ n p, lookup n = some p → p.ValidFor applies) :
    ∀ cert ∈ certs, ∀ z, applies z → CellCornerMargins cert.cell cert.margins z := by
  obtain ⟨hlen, hlinks⟩ := Bool.and_eq_true_iff.mp hgrid
  have hlen : certs.length = links.length := of_decide_eq_true hlen
  intro cert hc z hz
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hc
  have hnl : n < links.length := hlen ▸ hn
  have hnz : n < (certs.zip links).length := by simpa only [List.length_zip, ← hlen, Nat.min_self] using hn
  have hmem : (certs[n], links[n]) ∈ certs.zip links := by
    simpa only [List.getElem_zip] using (List.getElem_mem hnz)
  exact sideCornerLinksLookup_sound (List.all_eq_true.mp hlinks _ hmem) hpoints hz

abbrev sideCornerLinksOK (ps : Array SideCornerEntry) :=
  sideCornerLinksLookupOK (fun n => ps[n]?)

abbrev sideCornerGridOK (ps : Array SideCornerEntry) :=
  sideCornerGridLookupOK (fun n => ps[n]?)

private theorem valid_for_index {applies : Row → Prop} {ps : Array SideCornerEntry}
    (hpoints : ∀ n, ∀ hn : n < ps.size, ps[n].ValidFor applies) {n : Nat} {p : SideCornerEntry}
    (h : ps[n]? = some p) : p.ValidFor applies := by
  obtain ⟨hn, he⟩ := Array.getElem?_eq_some_iff.mp h
  exact he ▸ hpoints n hn

theorem sideCornerLinks_sound {ps : Array SideCornerEntry} {cert : CurvatureCellCertificate}
    {links : Vector Nat 8} {applies : Row → Prop} (hlinks : sideCornerLinksOK ps cert links = true)
    (hpoints : ∀ n, ∀ hn : n < ps.size, (ps[n]).ValidFor applies) {z : Row} (hz : applies z) :
    CellCornerMargins cert.cell cert.margins z :=
  sideCornerLinksLookup_sound hlinks (fun _ _ => valid_for_index hpoints) hz

theorem sideCornerGrid_sound {ps : Array SideCornerEntry} {certs : List CurvatureCellCertificate}
    {links : List (Vector Nat 8)} {applies : Row → Prop} (hgrid : sideCornerGridOK ps certs links = true)
    (hpoints : ∀ n, ∀ hn : n < ps.size, (ps[n]).ValidFor applies) :
    ∀ cert ∈ certs, ∀ z, applies z → CellCornerMargins cert.cell cert.margins z :=
  sideCornerGridLookup_sound hgrid (fun _ _ => valid_for_index hpoints)

/-- The point proofs can be assembled in the same blocks as the rational table. -/
def SideCornerEntriesOK (applies : Row → Prop) : List SideCornerEntry → Prop
  | [] => True
  | p :: ps => p.ValidFor applies ∧ SideCornerEntriesOK applies ps

theorem sideCornerEntriesOK_append {applies : Row → Prop} {xs ys : List SideCornerEntry}
    (hx : SideCornerEntriesOK applies xs) (hy : SideCornerEntriesOK applies ys) :
    SideCornerEntriesOK applies (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons x xs ih => exact ⟨hx.1, ih hx.2⟩

theorem sideCornerEntriesOK_get {applies : Row → Prop} {xs : List SideCornerEntry}
    (h : SideCornerEntriesOK applies xs) (n : Nat) (hn : n < xs.length) :
    xs[n].ValidFor applies := by
  induction xs generalizing n with
  | nil => simp at hn
  | cons p ps ih =>
    cases n with
    | zero => exact h.1
    | succ n => exact ih h.2 n (Nat.lt_of_succ_lt_succ hn)

theorem sideCornerEntriesOK_array_get {applies : Row → Prop} {ps : Array SideCornerEntry}
    (h : SideCornerEntriesOK applies ps.toList) (n : Nat) (hn : n < ps.size) :
    ps[n].ValidFor applies := by
  simpa only [Array.getElem_toList] using sideCornerEntriesOK_get h n
    (show n < ps.toList.length by simpa using hn)

theorem sideCornerEntriesOK_mem {applies : Row → Prop} {xs : List SideCornerEntry}
    (h : SideCornerEntriesOK applies xs) {p : SideCornerEntry} (hp : p ∈ xs) :
    p.ValidFor applies := by
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hp
  exact sideCornerEntriesOK_get h n hn

def sideCornerBlockLookup (blocks : List (Array SideCornerEntry)) (n : Nat) : Option SideCornerEntry :=
  (blocks[n / 32]?).bind fun b => b[n % 32]?

theorem sideCornerBlockLookup_mem {blocks : List (Array SideCornerEntry)} {n : Nat} {p : SideCornerEntry}
    (h : sideCornerBlockLookup blocks n = some p) : p ∈ blocks.flatMap Array.toList := by
  obtain ⟨b, hb, hp⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hbi, rfl⟩ := List.getElem?_eq_some_iff.mp hb
  obtain ⟨hpi, rfl⟩ := Array.getElem?_eq_some_iff.mp hp
  exact List.mem_flatMap.mpr ⟨_, List.getElem_mem hbi, Array.getElem_mem_toList hpi⟩

end HlawkaSchatten.BelowExponent.Vertex
