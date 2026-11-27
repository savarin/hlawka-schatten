/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Tangent.FaceJoin

set_option autoImplicit true
set_option relaxedAutoImplicit true

@[expose] public section

/- The original arithmetic soundness proof was written in the alpha-70 Lean pilot. -/

/-!
# Integer soundness for the bulk tangent checker

`tabOK_spec` proves the integer power bounds for every lookup-table entry.
`rcoef_spec` and `acoef_spec` bound the rounded tangent coefficients. The corner and leaf
lemmas give the inequalities on a single box, and `walk_sound` reconstructs a bisection
tree whose leaves satisfy them. The module `HlawkaSchatten.BelowExponent.Tangent.Real` interprets these bounds
with real weights and uses convexity to pass from vertices to profiles.
-/

namespace HlawkaSchatten.BelowExponent.TC

theorem ble_true {a b : Nat} : Nat.ble a b = true ↔ a ≤ b := by rw [Nat.ble_eq]

theorem blt_true {a b : Nat} : Nat.blt a b = true ↔ a < b := by
  simp [Nat.blt, Nat.ble_eq]; omega

theorem ble_dec (a b : Nat) : Nat.ble a b = decide (a ≤ b) :=
  Bool.eq_iff_iff.2 (by simp [Nat.ble_eq])

theorem blt_dec (a b : Nat) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.2 (by simp [Nat.blt, Nat.ble_eq]; omega)

theorem cdiv_spec (a b : Nat) (hb : 0 < b) : a ≤ cdiv a b * b := by
  unfold cdiv
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  rw [Nat.mul_comm]
  generalize b * ((a + b - 1) / b) = x at *
  omega

/-- D3, r-nodes, cleared denominators.  With R = p/2^K0 · 3^(h-e), A = An/2^K, B = Bn/2^K, r = m 4^-e:
    e ≤ h:  An k1 ≥ p 3^(h-e) (k1 - n1/2) 2^(K-K0),   Bn (2 k2 m) ≥ p 3^(h-e) n2 2^(K-K0) 4^e;
    e > h:  An k1 3^(e-h) ≥ p (k1 - n1/2) 2^(K-K0),   Bn (2 k2 m 3^(e-h)) ≥ p n2 2^(K-K0) 4^e. -/
theorem rcoef_spec (C : Ctx) (p m e : Nat) (hda : 0 < C.da) (hdb : 0 < C.db) (hm : 0 < m) :
    (e ≤ C.h → p * 3 ^ (C.h - e) * C.ca ≤ (rcoef C p m e).1 * C.da ∧
               (p * 3 ^ (C.h - e) * C.cb) <<< (2 * e) ≤ (rcoef C p m e).2 * (C.db * m)) ∧
    (C.h < e → p * C.ca ≤ (rcoef C p m e).1 * (C.da * 3 ^ (e - C.h)) ∧
               (p * C.cb) <<< (2 * e) ≤ (rcoef C p m e).2 * (C.db * m * 3 ^ (e - C.h))) := by
  have h3 : 0 < 3 ^ (e - C.h) := Nat.pow_pos (by decide)
  refine ⟨fun he => ?_, fun he => ?_⟩
  · have : Nat.ble e C.h = true := ble_true.2 he
    simp only [rcoef, this, Bool.cond_true]
    exact ⟨cdiv_spec _ _ hda, cdiv_spec _ _ (Nat.mul_pos hdb hm)⟩
  · have : Nat.ble e C.h = false := by
      cases h : Nat.ble e C.h
      · rfl
      · exact absurd (ble_true.1 h) (by omega)
    simp only [rcoef, this, Bool.cond_false]
    exact ⟨cdiv_spec _ _ (Nat.mul_pos hda h3), cdiv_spec _ _ (Nat.mul_pos (Nat.mul_pos hdb hm) h3)⟩

theorem lint_cons_eq_reference (C : Ctx) (Y : Nat) (sa : Bool) (ua : Nat)
    (sb : Bool) (ub : Nat) (t : Tm) (ts : List Tm) :
    lint C Y sa ua sb ub (t :: ts) = tmVal C Y sa ua sb ub t + lint C Y sa ua sb ub ts := by rfl

theorem acoef_eq_reference (C : Ctx) (code : Nat) :
    acoef C code =
  if code = 0 then (0, 0) else
  let i := (code - 1) % 64
  let m := 64 + i
  let e := 6 + (code - 1) / 64
  let ql := field C.Qlo C.W i
  let qh := field C.Qhi C.W i
  let Cneg := if e ≤ 7 then cdiv ((C.n2k2 * qh * 3 ^ (7 - e)) <<< C.sh) C.k2
              else cdiv ((C.n2k2 * qh) <<< C.sh) (C.k2 * 3 ^ (e - 7))
  let Dn := ((C.n1 * ql) <<< (e + C.sh)) / (C.k1 * m * 3 ^ (e - 6))
  (Cneg, Dn) := by rfl

/-- D3, a-nodes, cleared denominators (code ≥ 1; m = 64 + i, e = 6 + (code-1)/64, i = (code-1) % 64):
    Cneg k2 [3^(e-7)] ≥ (n2 - k2) Qhi [3^(7-e)] 2^(K-K0)  and  Dn k1 m 3^(e-6) ≤ n1 Qlo 2^e 2^(K-K0). -/
theorem acoef_spec (C : Ctx) (code : Nat) (hk1 : 0 < C.k1) (hk2 : 0 < C.k2) (hc : code ≠ 0) :
    let i := (code - 1) % 64
    let e := 6 + (code - 1) / 64
    let ql := field C.Qlo C.W i
    let qh := field C.Qhi C.W i
    (e ≤ 7 → (C.n2k2 * qh * 3 ^ (7 - e)) <<< C.sh ≤ (acoef C code).1 * C.k2) ∧
    (7 < e → (C.n2k2 * qh) <<< C.sh ≤ (acoef C code).1 * (C.k2 * 3 ^ (e - 7))) ∧
    (acoef C code).2 * (C.k1 * (64 + i) * 3 ^ (e - 6)) ≤ (C.n1 * ql) <<< (e + C.sh) := by
  intro i e ql qh
  have hcode : (code = 0) = False := by simp [hc]
  have h3 : 0 < 3 ^ (e - 7) := Nat.pow_pos (by decide)
  have h3' : 0 < C.k1 * (64 + i) * 3 ^ (e - 6) :=
    Nat.mul_pos (Nat.mul_pos hk1 (by omega)) (Nat.pow_pos (by decide))
  refine ⟨fun he => ?_, fun he => ?_, ?_⟩
  · simp only [acoef_eq_reference, hcode, ite_false]
    rw [ite_eq_left he]
    exact cdiv_spec _ _ hk2
  · simp only [acoef_eq_reference, hcode, ite_false]
    rw [ite_eq_right (by omega)]
    exact cdiv_spec _ _ (Nat.mul_pos hk2 h3)
  · simp only [acoef_eq_reference, hcode, ite_false]
    exact Nat.div_mul_le_self _ _

theorem p1OK_spec (P : Prof) (T : Tab) (n : Nat) (h : p1OK P T n = true) :
    ∀ i < n, 0 < field T.P1 T.W i ∧
      (2 ^ (P.MR - 2) + i) ^ (P.n1 / 2) * 2 ^ (P.K0 * P.k1) ≤
        field T.P1 T.W i ^ P.k1 * 2 ^ (P.MR * (P.n1 / 2)) := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    simp only [p1OK, Bool.and_eq_true, blt_true, ble_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact ih h3 i hi
    · subst hi; exact ⟨h1, h2⟩

theorem qOK_spec (P : Prof) (T : Tab) (n : Nat) (h : qOK P T n = true) :
    ∀ i < n,
      field T.Qlo T.W i ^ P.k1 * 2 ^ (6 * P.n1) ≤ (64 + i) ^ P.n1 * 2 ^ (P.K0 * P.k1) ∧
      (64 + i) ^ P.n1 * 2 ^ (P.K0 * P.k1) ≤ field T.Qhi T.W i ^ P.k1 * 2 ^ (7 * P.n1) := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    simp only [qOK, Bool.and_eq_true, ble_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact ih h3 i hi
    · subst hi; exact ⟨h1, h2⟩

/-- what `tabOK` guarantees (D1 bracket + every table slot) -/
theorem tabOK_spec (P : Prof) (T : Tab) (h : tabOK P T = true) :
    2 ^ P.n1 < 3 ^ P.k1 ∧ 3 ^ P.k2 < 2 ^ P.n2 ∧ P.n1 % 2 = 0 ∧ P.MR % 2 = 0 ∧ 4 ≤ P.MR ∧ P.K0 ≤ P.K ∧
    (∀ i < 3 * 2 ^ (P.MR - 2), 0 < field T.P1 T.W i ∧
      (2 ^ (P.MR - 2) + i) ^ (P.n1 / 2) * 2 ^ (P.K0 * P.k1) ≤
        field T.P1 T.W i ^ P.k1 * 2 ^ (P.MR * (P.n1 / 2))) ∧
    (∀ i < 64,
      field T.Qlo T.W i ^ P.k1 * 2 ^ (6 * P.n1) ≤ (64 + i) ^ P.n1 * 2 ^ (P.K0 * P.k1) ∧
      (64 + i) ^ P.n1 * 2 ^ (P.K0 * P.k1) ≤ field T.Qhi T.W i ^ P.k1 * 2 ^ (7 * P.n1)) := by
  simp only [tabOK, Bool.and_eq_true, blt_true, ble_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, p1OK_spec P T _ h7, qOK_spec P T _ h8⟩

theorem pick_range (C : Ctx) (m e : Nat) (h : C.mlo < C.mhi) :
    C.mlo ≤ (bif Nat.ble C.mhi m then (C.mlo, e - 1) else bif Nat.blt m C.mlo then (C.mlo, e) else (m, e)).1 ∧
    (bif Nat.ble C.mhi m then (C.mlo, e - 1) else bif Nat.blt m C.mlo then (C.mlo, e) else (m, e)).1 < C.mhi := by
  simp only [ble_dec, blt_dec, Bool.cond_decide]
  split <;> (try split) <;> simp only <;> omega

/-- the node has a table slot: mlo ≤ m < mhi -/
theorem node_range (C : Ctx) (X Y : Nat) (h : C.mlo < C.mhi) :
    C.mlo ≤ (node C X Y).1 ∧ (node C X Y).1 < C.mhi :=
  pick_range C ((2 * (X <<< (2 * esearch C.h X (Y <<< (C.MR - 2)))) + Y) / (2 * Y))
    (esearch C.h X (Y <<< (C.MR - 2))) h

def sgn (b : Bool) : Int := if b then 1 else -1

/-- the signed numerator g_n = ±c0 ± c1 |a| ± c2 |b| that `tmVal` takes the absolute value of -/
def gInt (t : Tm) (sa : Bool) (ua : Nat) (sb : Bool) (ub : Nat) : Int :=
  sgn t.s0 * t.c0 + sgn (beqB t.s1 sa) * (t.c1 * ua : Nat) + sgn (beqB t.s2 sb) * (t.c2 * ub : Nat)

theorem sgn_beqB (x y : Bool) : sgn (beqB x y) = sgn x * sgn y := by
  cases x <;> cases y <;> rfl

/-- the absolute value computed in `tmVal` (same expression) -/
def agOf (t : Tm) (sa : Bool) (ua : Nat) (sb : Bool) (ub : Nat) : Nat :=
  let t1 := t.c1 * ua
  let t2 := t.c2 * ub
  let g1 := beqB t.s1 sa
  let g2 := beqB t.s2 sb
  let P := (bif t.s0 then t.c0 else 0) + (bif g1 then t1 else 0) + (bif g2 then t2 else 0)
  let N := (bif t.s0 then 0 else t.c0) + (bif g1 then 0 else t1) + (bif g2 then 0 else t2)
  bif Nat.ble N P then P - N else N - P

theorem tmVal_eq (C : Ctx) (Y : Nat) (sa : Bool) (ua : Nat) (sb : Bool) (ub : Nat) (t : Tm) :
    tmVal C Y sa ua sb ub t = t.p * termL C (agOf t sa ua sb ub * agOf t sa ua sb ub) Y := rfl

theorem absdiff (P N : Nat) : ((bif Nat.ble N P then P - N else N - P : Nat) : Int) = ((P : Int) - N).natAbs := by
  simp only [ble_dec, Bool.cond_decide]
  split <;> omega

theorem ag_spec (t : Tm) (sa : Bool) (ua : Nat) (sb : Bool) (ub : Nat) :
    (agOf t sa ua sb ub : Int) = (gInt t sa ua sb ub).natAbs := by
  unfold agOf
  rw [absdiff]
  congr 1
  unfold gInt
  generalize beqB t.s1 sa = g1
  generalize beqB t.s2 sb = g2
  generalize t.c1 * ua = t1
  generalize t.c2 * ub = t2
  cases t.s0 <;> cases g1 <;> cases g2 <;> simp only [sgn, Bool.cond_true, Bool.cond_false] <;> simp <;> omega

theorem nmax_ge (a b : Nat) : a ≤ nmax a b ∧ b ≤ nmax a b := by
  unfold nmax
  simp only [ble_dec, Bool.cond_decide]
  split <;> omega

theorem lmaxV_ge (C : Ctx) (Y : Nat) (sa : Bool) (ua : Nat) (sb : Bool) (ub : Nat) (l : List (List Tm)) :
    ∀ ts ∈ l, lint C Y sa ua sb ub ts ≤ lmaxV C Y sa ua sb ub l := by
  induction l with
  | nil => intro ts h; cases h
  | cons hd tl ih =>
    intro ts h
    simp only [lmaxV]
    have := nmax_ge (lint C Y sa ua sb ub hd) (lmaxV C Y sa ua sb ub tl)
    rcases List.mem_cons.1 h with h | h
    · subst h; exact this.1
    · exact Nat.le_trans (ih ts h) this.2

theorem cornerOK_spec (C : Ctx) (F : Face) (add Dna Dnb A B Lc : Nat) :
    cornerOK C F add Dna Dnb A B Lc = true ↔
      Lc + add ≤ (F.gj2K + F.gk * Dna * (bif Nat.ble C.Da A then A - C.Da else C.Da - A) +
        F.gl * Dnb * (bif Nat.ble C.Da B then B - C.Da else C.Da - B)) * F.F := by
  simp [cornerOK]

theorem leafOK_spec (C : Ctx) (F : Face) (A1 A2 B1 B2 ca cb L11 L12 L21 L22 : Nat)
    (h : leafOK C F A1 A2 B1 B2 ca cb L11 L12 L21 L22 = true) :
    (C.Da ≤ A1 ∨ A2 ≤ C.Da) ∧ (C.Da ≤ B1 ∨ B2 ≤ C.Da) ∧
    let add := (F.gk * (acoef C ca).1 + F.gl * (acoef C cb).1) * C.Da * F.F
    cornerOK C F add (acoef C ca).2 (acoef C cb).2 A1 B1 L11 = true ∧
    cornerOK C F add (acoef C ca).2 (acoef C cb).2 A1 B2 L12 = true ∧
    cornerOK C F add (acoef C ca).2 (acoef C cb).2 A2 B1 L21 = true ∧
    cornerOK C F add (acoef C ca).2 (acoef C cb).2 A2 B2 L22 = true := by
  unfold leafOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, ble_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  revert h3
  cases acoef C ca
  cases acoef C cb
  intro ⟨⟨⟨a, b⟩, c⟩, d⟩
  exact ⟨a, b, c, d⟩

/-- a complete bisection tree of the box [A1,A2] x [B1,B2] (offset coordinates) whose leaves satisfy `P` -/
inductive BoxCover (P : Nat → Nat → Nat → Nat → Prop) : Nat → Nat → Nat → Nat → Prop
  | leaf {A1 A2 B1 B2 : Nat} : P A1 A2 B1 B2 → BoxCover P A1 A2 B1 B2
  | splitA {A1 A2 B1 B2 : Nat} (M : Nat) : A1 ≤ M → M ≤ A2 →
      BoxCover P A1 M B1 B2 → BoxCover P M A2 B1 B2 → BoxCover P A1 A2 B1 B2
  | splitB {A1 A2 B1 B2 : Nat} (M : Nat) : B1 ≤ M → M ≤ B2 →
      BoxCover P A1 A2 B1 M → BoxCover P A1 A2 M B2 → BoxCover P A1 A2 B1 B2

/-- the leaf property: some node codes make the leaf pass with the true corner values -/
def LeafP (C : Ctx) (F : Face) (A1 A2 B1 B2 : Nat) : Prop :=
  ∃ ca cb, leafOK C F A1 A2 B1 B2 ca cb
    (lmaxAt C F A1 B1) (lmaxAt C F A1 B2) (lmaxAt C F A2 B1) (lmaxAt C F A2 B2) = true

theorem walk_sound (C : Ctx) (F : Face) (fuel : Nat) :
    ∀ s A1 A2 B1 B2 s', A1 ≤ A2 → B1 ≤ B2 →
      walk C F fuel s A1 A2 B1 B2 (lmaxAt C F A1 B1) (lmaxAt C F A1 B2)
        (lmaxAt C F A2 B1) (lmaxAt C F A2 B2) = (true, s') →
      BoxCover (LeafP C F) A1 A2 B1 B2 := by
  induction fuel with
  | zero => intro s A1 A2 B1 B2 s' _ _ h; simp [walk] at h
  | succ fuel ih =>
    intro s A1 A2 B1 B2 s' hA hB h
    simp only [walk] at h
    split at h
    · -- split a
      split at h
      · rename_i s1 h1
        exact BoxCover.splitA _ (by omega) (by omega)
          (ih _ _ _ _ _ _ (by omega) hB h1) (ih _ _ _ _ _ _ (by omega) hB h)
      · cases h
    · split at h
      · split at h
        · rename_i s1 h1
          exact BoxCover.splitB _ (by omega) (by omega)
            (ih _ _ _ _ _ _ hA (by omega) h1) (ih _ _ _ _ _ _ hA (by omega) h)
        · cases h
      · split at h
        · simp only [Prod.mk.injEq] at h
          exact BoxCover.leaf ⟨_, _, h.1⟩
        · cases h

/-- what a passing face gives: a complete box tree of [0, 2 Da]² with passing leaves -/
theorem faceOK_sound (C : Ctx) (F : Face) (KBOX stream : Nat) (h : faceOK C F KBOX stream = true) :
    BoxCover (LeafP C F) 0 (2 * C.Da) 0 (2 * C.Da) := by
  unfold faceOK at h
  simp only [Bool.and_eq_true] at h
  have hw : walk C F (2 * KBOX + 4) stream 0 (2 * C.Da) 0 (2 * C.Da) (lmaxAt C F 0 0)
      (lmaxAt C F 0 (2 * C.Da)) (lmaxAt C F (2 * C.Da) 0) (lmaxAt C F (2 * C.Da) (2 * C.Da)) =
      (true, (walk C F (2 * KBOX + 4) stream 0 (2 * C.Da) 0 (2 * C.Da) (lmaxAt C F 0 0)
      (lmaxAt C F 0 (2 * C.Da)) (lmaxAt C F (2 * C.Da) 0) (lmaxAt C F (2 * C.Da) (2 * C.Da))).2) := by
    rw [← h.1]
  exact walk_sound C F _ _ _ _ _ _ _ (Nat.zero_le _) (Nat.zero_le _) hw

/-- what a passing cell gives: admissible integer weights, a sane geometry, and three complete face covers -/
theorem cellOK_spec (H : Hdr) (G : Geom) (D : CellData) (h : cellOK H G D = true) :
    ∃ p0 p1 p2 p3 g0 g1 g2, D.p = [p0, p1, p2, p3] ∧ D.g = [g0, g1, g2] ∧
      0 < H.Dw ∧ p0 + p1 + p2 + p3 = H.Dw ∧ g0 + g1 + g2 ≤ H.Dw ∧ geomOK G = true ∧
      BoxCover (LeafP (mkCtx H) (mkFace (mkCtx H) (cellVerts G).1 (cellVerts G).2 D.p D.g 0 1 2))
        0 (2 * (mkCtx H).Da) 0 (2 * (mkCtx H).Da) ∧
      BoxCover (LeafP (mkCtx H) (mkFace (mkCtx H) (cellVerts G).1 (cellVerts G).2 D.p D.g 1 0 2))
        0 (2 * (mkCtx H).Da) 0 (2 * (mkCtx H).Da) ∧
      BoxCover (LeafP (mkCtx H) (mkFace (mkCtx H) (cellVerts G).1 (cellVerts G).2 D.p D.g 2 0 1))
        0 (2 * (mkCtx H).Da) 0 (2 * (mkCtx H).Da) := by
  unfold cellOK at h
  split at h
  · rename_i p0 p1 p2 p3 g0 g1 g2 hp hg
    simp only [Bool.and_eq_true, blt_true, ble_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    revert h5
    rcases cellVerts G with ⟨V, Dn⟩
    intro h5
    obtain ⟨⟨f1, f2⟩, f3⟩ := h5
    rw [hp, hg] at *
    exact ⟨p0, p1, p2, p3, g0, g1, g2, rfl, rfl, h1, h2, h3, h4,
      faceOK_sound _ _ _ _ f1, faceOK_sound _ _ _ _ f2, faceOK_sound _ _ _ _ f3⟩
  · cases h


/-- The checked partition yields exactly the listed non-centre leaf geometries, in order. -/
theorem walkCT_eq_of_treeOK {H : Hdr} {tree : CT} {geoms : List Geom}
    (h : treeOK H tree geoms = true) : walkCT H tree (root H) = some geoms := by
  cases hw : walkCT H tree (root H) with
  | none => simp [treeOK, hw] at h
  | some found =>
    simp only [treeOK, hw, Bool.and_eq_true, beq_iff_eq] at h
    exact congrArg some h.2

/-- A numeric proof for each corresponding geometry and witness. -/
def CertifiedCells (H : Hdr) : List Geom → List CellData → Prop
  | [], [] => True
  | geom :: gs, data :: ds => (cellOK H geom data = true) ∧ CertifiedCells H gs ds
  | _, _ => False

theorem CertifiedCells.getD {H : Hdr} {geoms : List Geom} {cells : List CellData}
    (checked : CertifiedCells H geoms cells) {i : Nat} (hi : i < geoms.length) :
    cellOK H (geoms.getD i default) (cells.getD i default) = true := by
  induction geoms generalizing cells i with
  | nil => simp at hi
  | cons geom geoms ih =>
    cases cells with
    | nil => exact False.elim checked
    | cons data cells =>
      cases i with
      | zero => exact checked.1
      | succ i => exact ih checked.2 (Nat.lt_of_succ_lt_succ hi)

end HlawkaSchatten.BelowExponent.TC
