/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Original implementation by the alpha-70 Lean pilot for c1’s tangent certificate (2026-11-21). -/

/-!
# Integer checks for the bulk tangent certificate

`cellOK` checks a tangent certificate for the critical row inequality at `q = log₂ 3`.
Natural numbers represent the magnitudes and Boolean bits carry the signs. It verifies the
weights, profile vertices and the bisection tree on each normalized coordinate face.

  * weights: p0+p1+p2+p3 = Dw, g0+g1+g2 <= Dw  (pi = p/Dw, gamma = g/Dw);
  * the cell: the cone cell of `G` (triangle b1 b2 b3 over Db, lam in [l1n/l1d, l2n/l2d]); its vertices
    t^v = V_v / D are computed by `cellVerts`;
  * for each face j (x_j = 1, (a,b) = (x_k, x_l) in units 1/Da, Da = 2^KBOX, stored as A = a + Da in [0, 2 Da]):
    the packed stream decodes to a complete bisection tree of the square; every leaf box is sign-constant and,
    for its a-node codes (ca, cb), every corner (a,b) and every cell vertex v:
        sum_s p_s * termL(X_s, Y)  +  (g_k Cneg_a + g_l Cneg_b) Da F   <=   (g_j 2^K Da + g_k Dn_a |a| + g_l Dn_b |b|) F
    with g_n = numerator of g_s(t^v, x(c)) over D Da, X_s = g_n^2, Y = (D Da)^2, F = D^2 Da,
    termL(X,Y) = An Y + Bn X for the r-node (m,e) nearest X/Y (An, Bn from the P1 table), 0 if X = 0.
  The shared check `tabOK` validates the table entries by integer power comparisons.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.TC

structure Prof where
  n1 : Nat   -- n1/k1 < q = log2 3   (n1 even)
  k1 : Nat
  n2 : Nat   -- q < n2/k2
  k2 : Nat
  MR : Nat   -- r-ladder mantissa bits (even)
  K0 : Nat   -- table entries are numerators over 2^K0
  K : Nat    -- tangent coefficients are numerators over 2^K

structure Tab where
  W : Nat    -- field width of the packed tables
  P1 : Nat   -- slot i: p with p/2^K0 >= (m/2^MR)^(n1/(2 k1)),  m = 2^(MR-2) + i
  Qlo : Nat  -- slot i: p with p/2^K0 <= (m/64)^(n1/k1),         m = 64 + i
  Qhi : Nat  -- slot i: p with p/2^K0 >= (m/128)^(n1/k1),        m = 64 + i

structure Hdr where
  prof : Prof
  tab : Tab
  Dw : Nat
  KBOX : Nat
  CB : Nat
  rcN : Nat
  rcD : Nat
  etaN : Nat
  etaD : Nat

abbrev P3 := Nat × Nat × Nat

structure Geom where
  b : List P3          -- the three base points (b1, b2, b3) numerators over Db (fourth coordinate 0)
  Db : Nat
  l1n : Nat
  l1d : Nat
  l2n : Nat
  l2d : Nat
deriving Inhabited, DecidableEq, Repr

structure CellData where
  p : List Nat         -- pi numerators (4), over Dw
  g : List Nat         -- gamma numerators (3), over Dw
  f1 : Nat             -- packed box tree of face x1 = 1
  f2 : Nat
  f3 : Nat
deriving Inhabited

/-- field `i` of width `W` of a packed table -/
def field (T W i : Nat) : Nat := (T >>> (W * i)) % 2 ^ W

/-- ceiling division -/
def cdiv (a b : Nat) : Nat := (a + b - 1) / b

/-! Kernel-speed conventions (measured, see report.md): comparisons are `bif` on `Nat.ble`/`Nat.blt`/`Nat.beq`
inside small NON-recursive helpers (about 2x faster than `if` on a decidable Prop; a direct `Nat.ble` inside the
body of a recursive function is 40-60x slower), and recursive functions only call such helpers. -/

def nmax (a b : Nat) : Nat := bif Nat.ble a b then b else a

/-- Bool equality by cases (avoids the `DecidableEq Bool` instance) -/
def beqB : Bool → Bool → Bool
  | true, b => b
  | false, b => !b

/-! ## Tables (c1 D1, D2): checked once per profile -/

def p1OK (P : Prof) (T : Tab) : Nat → Bool
  | 0 => true
  | i + 1 =>
    let m := 2 ^ (P.MR - 2) + i
    let p := field T.P1 T.W i
    Nat.blt 0 p &&
    Nat.ble (m ^ (P.n1 / 2) * 2 ^ (P.K0 * P.k1)) (p ^ P.k1 * 2 ^ (P.MR * (P.n1 / 2))) &&
    p1OK P T i

def qOK (P : Prof) (T : Tab) : Nat → Bool
  | 0 => true
  | i + 1 =>
    let m := 64 + i
    let ql := field T.Qlo T.W i
    let qh := field T.Qhi T.W i
    Nat.ble (ql ^ P.k1 * 2 ^ (6 * P.n1)) (m ^ P.n1 * 2 ^ (P.K0 * P.k1)) &&
    Nat.ble (m ^ P.n1 * 2 ^ (P.K0 * P.k1)) (qh ^ P.k1 * 2 ^ (7 * P.n1)) &&
    qOK P T i

def tabOK (P : Prof) (T : Tab) : Bool :=
  Nat.blt (2 ^ P.n1) (3 ^ P.k1) && Nat.blt (3 ^ P.k2) (2 ^ P.n2) &&
  P.n1 % 2 == 0 && P.MR % 2 == 0 && Nat.ble 4 P.MR && Nat.ble P.K0 P.K &&
  p1OK P T (3 * 2 ^ (P.MR - 2)) && qOK P T 64

/-! ## Derived constants -/

structure Ctx where
  MR : Nat
  mlo : Nat      -- 2^(MR-2)
  mhi : Nat      -- 2^MR
  h : Nat        -- MR/2
  ca : Nat       -- (k1 - n1/2) 2^(K-K0)
  da : Nat       -- k1
  cb : Nat       -- n2 2^(K-K0)
  db : Nat       -- 2 k2
  n2k2 : Nat     -- n2 - k2
  k2 : Nat
  n1 : Nat
  k1 : Nat
  sh : Nat       -- K - K0
  K : Nat
  W : Nat
  P1 : Nat
  Qlo : Nat
  Qhi : Nat
  CB : Nat
  Da : Nat

def mkCtx (H : Hdr) : Ctx :=
  let P := H.prof
  { MR := P.MR, mlo := 2 ^ (P.MR - 2), mhi := 2 ^ P.MR, h := P.MR / 2,
    ca := (P.k1 - P.n1 / 2) * 2 ^ (P.K - P.K0), da := P.k1,
    cb := P.n2 * 2 ^ (P.K - P.K0), db := 2 * P.k2, n2k2 := P.n2 - P.k2, k2 := P.k2,
    n1 := P.n1, k1 := P.k1, sh := P.K - P.K0, K := P.K,
    W := H.tab.W, P1 := H.tab.P1, Qlo := H.tab.Qlo, Qhi := H.tab.Qhi, CB := H.CB, Da := 2 ^ H.KBOX }

/-! ## r-nodes (upper tangents of s^(q/2)) and a-nodes (lower tangents of u^q), c1 D3 -/

/-- (An, Bn): A = An/2^K >= R (1 - n1/(2k1)), B = Bn/2^K >= R n2/(2 k2) / r,  R = p/2^K0 3^(MR/2 - e), r = m 4^-e -/
def rcoef (C : Ctx) (p m e : Nat) : Nat × Nat :=
  bif Nat.ble e C.h then
    let t := 3 ^ (C.h - e)
    (cdiv (p * t * C.ca) C.da, cdiv ((p * t * C.cb) <<< (2 * e)) (C.db * m))
  else
    let t := 3 ^ (e - C.h)
    (cdiv (p * C.ca) (C.da * t), cdiv ((p * C.cb) <<< (2 * e)) (C.db * m * t))

/-- (Cneg, Dn): C = -Cneg/2^K <= -(n2/k2 - 1) hi,  D = Dn/2^K <= (n1/k1) lo / a0;  a0 = m 2^-e,
    lo = Qlo/2^K0 3^(6-e) <= a0^q <= hi = Qhi/2^K0 3^(7-e).  Code 0 is the bound u^q >= 0. -/
def acoef (C : Ctx) (code : Nat) : Nat × Nat :=
  if code = 0 then (0, 0) else
  let i := (code - 1) % 64
  let m := 64 + i
  let e := 6 + (code - 1) / 64
  let ql := field C.Qlo C.W i
  let qh := field C.Qhi C.W i
  let Cneg := if e ≤ 7 then cdiv ((C.n2k2 * qh * 3 ^ (7 - e)) <<< C.sh) C.k2
              else cdiv ((C.n2k2 * qh) <<< C.sh) (C.k2 * 3 ^ (e - 7))
  let Dn := ((C.n1 * ql) <<< (e + C.sh)) / (C.k1 * m * 3 ^ (e - 6))
  (Cneg, Dn)

/-- f e := Ylo <= X 4^e (monotone in e) -/
def fe (X Ylo e : Nat) : Bool := Nat.ble Ylo (X <<< (2 * e))

/-- given f e: the smallest e' <= e with f e' -/
def eDown (X Ylo : Nat) : Nat → Nat
  | 0 => 0
  | e + 1 => bif fe X Ylo e then eDown X Ylo e else e + 1

/-- the first e' >= e with f e' (fuel-bounded) -/
def eUp (X Ylo : Nat) : Nat → Nat → Nat
  | 0, e => e
  | fuel + 1, e => bif fe X Ylo e then e else eUp X Ylo fuel (e + 1)

/-- the smallest e with f e, searched from e = h = MR/2 (85-90% of the nodes have e in h-1 .. h+2) -/
def esearch (h X Ylo : Nat) : Nat :=
  bif fe X Ylo h then
    (bif fe X Ylo (h - 1) then (bif fe X Ylo (h - 2) then eDown X Ylo (h - 2) else h - 1) else h)
  else
    (bif fe X Ylo (h + 1) then h + 1 else bif fe X Ylo (h + 2) then h + 2 else eUp X Ylo 128 (h + 3))

/-- the r-node (m, e), 2^(MR-2) <= m < 2^MR, with m 4^-e nearest to X/Y (c1's `choose_rnode`).
    Only a choice: soundness holds for every node. -/
def node (C : Ctx) (X Y : Nat) : Nat × Nat :=
  let Ylo := Y <<< (C.MR - 2)
  let e := esearch C.h X Ylo
  let m := (2 * (X <<< (2 * e)) + Y) / (2 * Y)
  bif Nat.ble C.mhi m then (C.mlo, e - 1)
  else bif Nat.blt m C.mlo then (C.mlo, e) else (m, e)

/-- An Y + Bn X  (an upper bound of (X/Y)^(q/2) times 2^K Y), and 0 for X = 0 -/
def termL (C : Ctx) (X Y : Nat) : Nat :=
  bif Nat.beq X 0 then 0 else
  match node C X Y with
  | (m, e) =>
    match rcoef C (field C.P1 C.W (m - C.mlo)) m e with
    | (An, Bn) => An * Y + Bn * X

/-! ## Geometry of a cone cell -/

structure V4 where
  v0 : Nat
  v1 : Nat
  v2 : Nat
  v3 : Nat
deriving Repr

/-- the vertex c + lam (b - c), lam = n/d, as numerators over D = 4 Db d o -/
def vtx (Db o d n : Nat) (b : P3) : V4 :=
  let base := Db * o * (d - n)
  let k := 4 * o * n
  ⟨base + k * b.1, base + k * b.2.1, base + k * b.2.2, base⟩

/-- the (distinct) vertices of the cell and their common denominator D = 4 Db l1d l2d -/
def cellVerts (G : Geom) : List V4 × Nat :=
  let inner := if G.l1n = 0 then [vtx G.Db G.l2d G.l1d 0 (0, 0, 0)] else G.b.map (vtx G.Db G.l2d G.l1d G.l1n)
  (inner ++ G.b.map (vtx G.Db G.l1d G.l2d G.l2n), 4 * G.Db * G.l1d * G.l2d)

/-- chi_i(s) = +1 ?   chi = (+,+,+), (-,-,+), (-,+,-), (+,-,-) -/
def chiPos : Nat → Nat → Bool
  | 0, _ => true
  | 1, i => i == 2
  | 2, i => i == 1
  | _, i => i == 0

/-- T_i(s) numerator: v_s + v_partner_i(s); matchings i=0: {0,3}{1,2}, i=1: {0,2}{1,3}, i=2: {0,1}{2,3} -/
def wv (v : V4) : Nat → Nat → Nat
  | 0, 0 => v.v0 + v.v3 | 0, 1 => v.v1 + v.v2 | 0, 2 => v.v2 + v.v1 | 0, _ => v.v3 + v.v0
  | 1, 0 => v.v0 + v.v2 | 1, 1 => v.v1 + v.v3 | 1, 2 => v.v2 + v.v0 | 1, _ => v.v3 + v.v1
  | _, 0 => v.v0 + v.v1 | _, 1 => v.v1 + v.v0 | _, 2 => v.v2 + v.v3 | _, _ => v.v3 + v.v2

/-- one member s at one vertex: g_n = (+-) c0 + (+-) c1 a + (+-) c2 b, weight p -/
structure Tm where
  c0 : Nat
  s0 : Bool
  c1 : Nat
  s1 : Bool
  c2 : Nat
  s2 : Bool
  p : Nat

def mkTm (Da : Nat) (v : V4) (j k l s p : Nat) : Tm :=
  ⟨wv v j s * Da, chiPos s j, wv v k s, chiPos s k, wv v l s, chiPos s l, p⟩

def mkTms (Da : Nat) (j k l : Nat) (ps : List Nat) (v : V4) : List Tm :=
  match ps with
  | [p0, p1, p2, p3] => [mkTm Da v j k l 0 p0, mkTm Da v j k l 1 p1, mkTm Da v j k l 2 p2, mkTm Da v j k l 3 p3]
  | _ => []

structure Face where
  Y : Nat
  F : Nat
  gj2K : Nat
  gk : Nat
  gl : Nat
  terms : List (List Tm)

/-! ## The corner inequality -/

/-- p_s (An Y + Bn X) for one member at the corner with signs sa, sb and magnitudes ua = |a|, ub = |b| -/
def tmVal (C : Ctx) (Y : Nat) (sa : Bool) (ua : Nat) (sb : Bool) (ub : Nat) (t : Tm) : Nat :=
  let t1 := t.c1 * ua
  let t2 := t.c2 * ub
  let g1 := beqB t.s1 sa
  let g2 := beqB t.s2 sb
  let P := (bif t.s0 then t.c0 else 0) + (bif g1 then t1 else 0) + (bif g2 then t2 else 0)
  let N := (bif t.s0 then 0 else t.c0) + (bif g1 then 0 else t1) + (bif g2 then 0 else t2)
  let ag := bif Nat.ble N P then P - N else N - P
  t.p * termL C (ag * ag) Y

def lint (C : Ctx) (Y : Nat) (sa : Bool) (ua : Nat) (sb : Bool) (ub : Nat) : List Tm → Nat
  | [] => 0
  | t :: ts => tmVal C Y sa ua sb ub t + lint C Y sa ua sb ub ts

/-- max over the cell vertices of  sum_s p_s (An Y + Bn X_s)  at one corner -/
def lmaxV (C : Ctx) (Y : Nat) (sa : Bool) (ua : Nat) (sb : Bool) (ub : Nat) : List (List Tm) → Nat
  | [] => 0
  | ts :: r => nmax (lint C Y sa ua sb ub ts) (lmaxV C Y sa ua sb ub r)

/-- the corner (A, B) (offset coordinates: a = A - Da) as sign bits and magnitudes -/
def lmaxAt (C : Ctx) (F : Face) (A B : Nat) : Nat :=
  let sa := Nat.ble C.Da A
  let sb := Nat.ble C.Da B
  lmaxV C F.Y sa (bif sa then A - C.Da else C.Da - A) sb (bif sb then B - C.Da else C.Da - B) F.terms

/-- L(corner) + (g_k Cneg_a + g_l Cneg_b) Da F  <=  (g_j 2^K Da + g_k Dn_a |a| + g_l Dn_b |b|) F -/
def cornerOK (C : Ctx) (F : Face) (lhsAdd Dna Dnb A B Lc : Nat) : Bool :=
  let ua := bif Nat.ble C.Da A then A - C.Da else C.Da - A
  let ub := bif Nat.ble C.Da B then B - C.Da else C.Da - B
  Nat.ble (Lc + lhsAdd) ((F.gj2K + F.gk * Dna * ua + F.gl * Dnb * ub) * F.F)

def leafOK (C : Ctx) (F : Face) (A1 A2 B1 B2 ca cb L11 L12 L21 L22 : Nat) : Bool :=
  (Nat.ble C.Da A1 || Nat.ble A2 C.Da) && (Nat.ble C.Da B1 || Nat.ble B2 C.Da) &&
  match acoef C ca, acoef C cb with
  | (Cna, Dna), (Cnb, Dnb) =>
    let add := (F.gk * Cna + F.gl * Cnb) * C.Da * F.F
    cornerOK C F add Dna Dnb A1 B1 L11 && cornerOK C F add Dna Dnb A1 B2 L12 &&
    cornerOK C F add Dna Dnb A2 B1 L21 && cornerOK C F add Dna Dnb A2 B2 L22

/-- walk the packed box tree (2-bit tags: 0 split a, 1 split b, 2 leaf + two CB-bit codes); returns the rest.
    Lxy = lmaxAt at corner (Ax, By) of the current box, computed once and handed down to the children
    (a split evaluates only its two new points). -/
def walk (C : Ctx) (F : Face) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool × Nat
  | 0, s, _, _, _, _, _, _, _, _ => (false, s)
  | fuel + 1, s, A1, A2, B1, B2, L11, L12, L21, L22 =>
    let tag := s % 4
    let s := s >>> 2
    if tag = 0 then
      let M := (A1 + A2) / 2
      let LM1 := lmaxAt C F M B1
      let LM2 := lmaxAt C F M B2
      match walk C F fuel s A1 M B1 B2 L11 L12 LM1 LM2 with
      | (true, s) => walk C F fuel s M A2 B1 B2 LM1 LM2 L21 L22
      | (false, s) => (false, s)
    else if tag = 1 then
      let M := (B1 + B2) / 2
      let L1M := lmaxAt C F A1 M
      let L2M := lmaxAt C F A2 M
      match walk C F fuel s A1 A2 B1 M L11 L1M L21 L2M with
      | (true, s) => walk C F fuel s A1 A2 M B2 L1M L12 L2M L22
      | (false, s) => (false, s)
    else if tag = 2 then
      (leafOK C F A1 A2 B1 B2 (s % 2 ^ C.CB) ((s >>> C.CB) % 2 ^ C.CB) L11 L12 L21 L22, s >>> (2 * C.CB))
    else (false, s)

def faceOK (C : Ctx) (F : Face) (KBOX stream : Nat) : Bool :=
  let T := 2 * C.Da
  match walk C F (2 * KBOX + 4) stream 0 T 0 T (lmaxAt C F 0 0) (lmaxAt C F 0 T) (lmaxAt C F T 0) (lmaxAt C F T T) with
  | (ok, rest) => ok && rest == 1

def mkFace (C : Ctx) (V : List V4) (D : Nat) (ps gs : List Nat) (j k l : Nat) : Face :=
  { Y := (D * C.Da) ^ 2, F := D * D * C.Da, gj2K := gs.getD j 0 * 2 ^ C.K * C.Da,
    gk := gs.getD k 0, gl := gs.getD l 0, terms := V.map (mkTms C.Da j k l ps) }

/-- sanity of the cell geometry (the tree walk guarantees it; kept so that a cell file stands alone) -/
def geomOK (G : Geom) : Bool :=
  G.b.length == 3 && Nat.blt 0 G.Db && Nat.blt 0 G.l1d && Nat.blt 0 G.l2d &&
  Nat.blt (G.l1n * G.l2d) (G.l2n * G.l1d) && Nat.ble G.l2n G.l2d &&
  G.b.all (fun b => b.1 + b.2.1 + b.2.2 == G.Db)

def cellOK (H : Hdr) (G : Geom) (D : CellData) : Bool :=
  match D.p, D.g with
  | [p0, p1, p2, p3], [g0, g1, g2] =>
    Nat.blt 0 H.Dw && p0 + p1 + p2 + p3 == H.Dw && Nat.ble (g0 + g1 + g2) H.Dw && geomOK G &&
    (let C := mkCtx H
     match cellVerts G with
     | (V, Dn) =>
       faceOK C (mkFace C V Dn D.p D.g 0 1 2) H.KBOX D.f1 &&
       faceOK C (mkFace C V Dn D.p D.g 1 0 2) H.KBOX D.f2 &&
       faceOK C (mkFace C V Dn D.p D.g 2 0 1) H.KBOX D.f3)
  | _, _ => false

/-! ## The cell tree (c1 Lemma 4): cone cells over the base triangle, leaves `c` (inside the centre cube) and `C` -/

inductive CT where
  | T : Nat → Nat → CT → CT → CT     -- bisect base edge (i, j); first child: b_i replaced by the midpoint
  | R : Nat → Nat → CT → CT → CT     -- radial split at lam = p/q; first child [lam1, p/q]
  | c : CT                           -- all vertices strictly inside the open cube max |t_i - 1/4| < rc
  | C : CT                           -- certified cell (its data is in a cell file)

def p3add (x y : P3) : P3 := (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2)
def p3dbl (x : P3) : P3 := (2 * x.1, 2 * x.2.1, 2 * x.2.2)
def p3half (x : P3) : P3 := (x.1 / 2, x.2.1 / 2, x.2.2 / 2)
def p3even (x : P3) : Bool := x.1 % 2 == 0 && x.2.1 % 2 == 0 && x.2.2 % 2 == 0

def setAt (l : List P3) (i : Nat) (x : P3) : List P3 := l.set i x

/-- tangential split of edge (i, j), with c1's normalisation (keep denominator Db when the midpoint is integral) -/
def tsplit (G : Geom) (i j : Nat) : Option (Geom × Geom) :=
  if i < 3 && j < 3 && i != j && G.b.length == 3 then
    let W := G.b.map p3dbl
    let mid := p3add (G.b.getD i (0, 0, 0)) (G.b.getD j (0, 0, 0))
    let ev := p3even mid      -- c1 halves when 2b and mid are all even, i.e. when mid is
    let W := if ev then G.b else W
    let mid := if ev then p3half mid else mid
    let Db := if ev then G.Db else 2 * G.Db
    some ({ G with b := setAt W i mid, Db := Db }, { G with b := setAt W j mid, Db := Db })
  else none

/-- all vertices strictly inside the open cube { max_i |t_i - 1/4| < rcN/rcD } -/
def inCube (H : Hdr) (G : Geom) : Bool :=
  match cellVerts G with
  | (V, D) =>
    let ok (x : Nat) : Bool :=
      Nat.blt ((if D ≤ 4 * x then 4 * x - D else D - 4 * x) * H.rcD) (4 * D * H.rcN)
    V.all (fun v => ok v.v0 && ok v.v1 && ok v.v2 && ok v.v3)

def walkCT (H : Hdr) : CT → Geom → Option (List Geom)
  | .T i j a b, G =>
    match tsplit G i j with
    | some (G1, G2) =>
      match walkCT H a G1, walkCT H b G2 with
      | some l1, some l2 => some (l1 ++ l2)
      | _, _ => none
    | none => none
  | .R p q a b, G =>
    if Nat.blt 0 q && Nat.blt (G.l1n * q) (p * G.l1d) && Nat.blt (p * G.l2d) (G.l2n * q) then
      match walkCT H a { G with l2n := p, l2d := q }, walkCT H b { G with l1n := p, l1d := q } with
      | some l1, some l2 => some (l1 ++ l2)
      | _, _ => none
    else none
  | .c, G => if inCube H G then some [] else none
  | .C, G => some [G]

/-- root: base triangle (1,0,0), (1/2,1/2,0), (1/3,1/3,1/3) over 6; lam in [0, 1 - 4 eta] -/
def root (H : Hdr) : Geom :=
  { b := [(6, 0, 0), (3, 3, 0), (2, 2, 2)], Db := 6, l1n := 0, l1d := 1,
    l2n := H.etaD - 4 * H.etaN, l2d := H.etaD }

def treeOK (H : Hdr) (t : CT) (gs : List Geom) : Bool :=
  Nat.blt 0 H.etaN && Nat.blt (4 * H.etaN) H.etaD && Nat.blt 0 H.rcN && Nat.blt 0 H.rcD &&
  match walkCT H t (root H) with
  | some l => l == gs
  | none => false

end HlawkaSchatten.BelowExponent.TC
