/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.DyadicBounds
public import HlawkaSchatten.BelowExponent.Vertex.CoefficientDerivatives

/-! Sound fixed-point evaluation of values and both parameter derivatives. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

namespace IntervalJet

def Contains (b : IntervalJet) (x : Jet) : Prop :=
  b.value.Contains x.value ∧ b.first.Contains x.first ∧ b.second.Contains x.second

theorem const_mem (q : ℚ) : (const q).Contains (Jet.const (q : ℝ)) := by
  have h₀ : (DyadicBounds.point 0).Contains (0 : ℝ) := by
    simpa only [Rat.cast_zero] using DyadicBounds.point_mem 0
  exact ⟨DyadicBounds.point_mem q, h₀, h₀⟩

theorem Contains.add {a b : IntervalJet} {x y : Jet} (ha : a.Contains x) (hb : b.Contains y) :
    (a.add b).Contains (x.add y) := ⟨ha.1.add hb.1, ha.2.1.add hb.2.1, ha.2.2.add hb.2.2⟩

theorem Contains.sub {a b : IntervalJet} {x y : Jet} (ha : a.Contains x) (hb : b.Contains y) :
    (a.sub b).Contains (x.sub y) := ⟨ha.1.sub hb.1, ha.2.1.sub hb.2.1, ha.2.2.sub hb.2.2⟩

theorem Contains.mul {a b : IntervalJet} {x y : Jet} (ha : a.Contains x) (hb : b.Contains y) :
    (a.mul b).Contains (x.mul y) := by
  have h₂ : (DyadicBounds.point 2).Contains (2 : ℝ) := by simpa using DyadicBounds.point_mem 2
  exact ⟨ha.1.mul hb.1, (ha.2.1.mul hb.1).add (ha.1.mul hb.2.1),
    ((ha.2.2.mul hb.1).add ((h₂.mul ha.2.1).mul hb.2.1)).add (ha.1.mul hb.2.2)⟩

theorem Contains.scale {a : IntervalJet} {x : Jet} (ha : a.Contains x) (r : ℚ) :
    (scale r a).Contains (Jet.scale (r : ℝ) x) :=
  ⟨(DyadicBounds.point_mem r).mul ha.1, (DyadicBounds.point_mem r).mul ha.2.1,
    (DyadicBounds.point_mem r).mul ha.2.2⟩

theorem sumThree_mem {f : Fin 3 → IntervalJet} {g : Fin 3 → Jet} (h : ∀ i, (f i).Contains (g i)) :
    (sumThree f).Contains (Jet.sumThree g) := ((h 0).add (h 1)).add (h 2)

theorem Contains.div {a b : IntervalJet} {x y : Jet} (ha : a.Contains x) (hb : b.Contains y) :
    (a.div b).Contains (x.div y) := by
  have h₂ : (DyadicBounds.point 2).Contains (2 : ℝ) := by simpa using DyadicBounds.point_mem 2
  have hv := ha.1.div hb.1
  have hd := (ha.2.1.sub (hv.mul hb.2.1)).div hb.1
  exact ⟨hv, hd, ((ha.2.2.sub (hv.mul hb.2.2)).sub ((h₂.mul hd).mul hb.2.1)).div hb.1⟩

theorem Contains.logFirst {a : IntervalJet} {x : Jet} (h : a.Contains x) : a.logFirst.Contains x.logFirst :=
  h.2.1.div h.1

theorem Contains.logSecond {a : IntervalJet} {x : Jet} (h : a.Contains x) : a.logSecond.Contains x.logSecond :=
  (h.2.2.div h.1).sub h.logFirst.square

theorem logRadicalFirst_mem {a b s : IntervalJet} {A B S : Jet}
    (ha : a.Contains A) (hb : b.Contains B) (hs : s.Contains S) :
    (logRadicalFirst a b s).Contains (Jet.logRadicalFirst A B S) := by
  have p (n : ℕ) : (DyadicBounds.point n).Contains (n : ℝ) := by simpa using DyadicBounds.point_mem n
  exact ((((p 2).mul ha.logFirst).add ((p 3).mul hb.logFirst)).sub ((p 2).mul hs.logFirst)).div (p 5)

theorem logRadicalSecond_mem {a b s : IntervalJet} {A B S : Jet}
    (ha : a.Contains A) (hb : b.Contains B) (hs : s.Contains S) :
    (logRadicalSecond a b s).Contains (Jet.logRadicalSecond A B S) := by
  have p (n : ℕ) : (DyadicBounds.point n).Contains (n : ℝ) := by simpa using DyadicBounds.point_mem n
  exact ((((p 2).mul ha.logSecond).add ((p 3).mul hb.logSecond)).sub ((p 2).mul hs.logSecond)).div (p 5)

theorem radical_mem {r : DyadicBounds} {a b s : IntervalJet} {A B S : Jet}
    (hr : r.Contains (Jet.radical A B S).value) (ha : a.Contains A) (hb : b.Contains B) (hs : s.Contains S) :
    (radical r a b s).Contains (Jet.radical A B S) := by
  have h := logRadicalFirst_mem ha hb hs
  have h' := logRadicalSecond_mem ha hb hs
  exact ⟨hr, hr.mul h, hr.mul (h.square.add h')⟩

end IntervalJet

end HlawkaSchatten.BelowExponent.Vertex
