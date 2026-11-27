/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.ParameterBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! First and second parameter derivatives of the actual VC and SC radicals. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

noncomputable section

/-- The value and two derivatives along a real parameter line. -/
@[ext] structure Jet where
  value : ℝ
  first : ℝ
  second : ℝ

namespace Jet

def const (x : ℝ) : Jet := ⟨x, 0, 0⟩

def add (x y : Jet) : Jet := ⟨x.value + y.value, x.first + y.first, x.second + y.second⟩

def sub (x y : Jet) : Jet := ⟨x.value - y.value, x.first - y.first, x.second - y.second⟩

def mul (x y : Jet) : Jet :=
  ⟨x.value * y.value, x.first * y.value + x.value * y.first,
    x.second * y.value + 2 * x.first * y.first + x.value * y.second⟩

def ValidAt (f : ℝ → Jet) (t : ℝ) : Prop :=
  HasDerivAt (fun x => (f x).value) (f t).first t ∧
    HasDerivAt (fun x => (f x).first) (f t).second t

theorem valid_const (z t : ℝ) : ValidAt (fun _ => const z) t :=
  ⟨hasDerivAt_const t z, hasDerivAt_const t (0 : ℝ)⟩

theorem ValidAt.add {f g : ℝ → Jet} {t : ℝ} (hf : ValidAt f t) (hg : ValidAt g t) :
    ValidAt (fun x => (f x).add (g x)) t :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem ValidAt.sub {f g : ℝ → Jet} {t : ℝ} (hf : ValidAt f t) (hg : ValidAt g t) :
    ValidAt (fun x => (f x).sub (g x)) t :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem ValidAt.mul {f g : ℝ → Jet} {t : ℝ} (hf : ValidAt f t) (hg : ValidAt g t) :
    ValidAt (fun x => (f x).mul (g x)) t := by
  refine ⟨hf.1.mul hg.1, ?_⟩
  have hs := (hf.2.mul hg.1).add (hf.1.mul hg.2)
  change HasDerivAt (fun x => (f x).first * (g x).value + (f x).value * (g x).first)
    ((f t).second * (g t).value + 2 * (f t).first * (g t).first + (f t).value * (g t).second) t
  convert hs using 1
  ring

def logFirst (u : Jet) : ℝ := u.first / u.value

def logSecond (u : Jet) : ℝ := u.second / u.value - (u.logFirst) ^ 2

theorem ValidAt.logFirst {f : ℝ → Jet} {t : ℝ} (hf : ValidAt f t) (h : (f t).value ≠ 0) :
    HasDerivAt (fun x => (f x).logFirst) (f t).logSecond t := by
  have hd := hf.2.div hf.1 h
  convert hd using 1
  · rfl
  · simp only [Jet.logSecond, Jet.logFirst]
    field_simp [h]

def logRadicalFirst (a b s : Jet) : ℝ := (2 * a.logFirst + 3 * b.logFirst - 2 * s.logFirst) / 5

def logRadicalSecond (a b s : Jet) : ℝ := (2 * a.logSecond + 3 * b.logSecond - 2 * s.logSecond) / 5

/-- The three positive factors of A²B³/S² require only one real fifth root. -/
def radical (a b s : Jet) : Jet :=
  let r := (a.value ^ 2 * b.value ^ 3 / s.value ^ 2) ^ (1 / 5 : ℝ)
  let h := logRadicalFirst a b s
  let h' := logRadicalSecond a b s
  ⟨r, r * h, r * (h ^ 2 + h')⟩

theorem ValidAt.radical {A B S : ℝ → Jet} {x : ℝ}
    (hA : ValidAt A x) (hB : ValidAt B x) (hS : ValidAt S x)
    (ha : 0 < (A x).value) (hb : 0 < (B x).value) (hs : 0 < (S x).value) :
    ValidAt (fun t => radical (A t) (B t) (S t)) x := by
  let W (t : ℝ) := (A t).value ^ 2 * (B t).value ^ 3 / (S t).value ^ 2
  let H (t : ℝ) := logRadicalFirst (A t) (B t) (S t)
  let R (t : ℝ) := (W t) ^ (1 / 5 : ℝ)
  have hW : 0 < W x := by
    dsimp [W]
    positivity
  have hW' : HasDerivAt W (W x * (5 * H x)) x := by
    have hd := ((hA.1.pow 2).mul (hB.1.pow 3)).div (hS.1.pow 2) (pow_ne_zero _ hs.ne')
    convert hd using 1
    dsimp [W, H, logRadicalFirst, Jet.logFirst]
    field_simp [ha.ne', hb.ne', hs.ne']
  have hR : HasDerivAt R (R x * H x) x := by
    have hd := hW'.rpow_const (p := (1 / 5 : ℝ)) (Or.inl hW.ne')
    convert hd using 1
    dsimp only [R]
    rw [Real.rpow_sub_one hW.ne']
    field_simp [hW.ne']
  have hH : HasDerivAt H (logRadicalSecond (A x) (B x) (S x)) x :=
    (((hA.logFirst ha.ne').const_mul 2).add ((hB.logFirst hb.ne').const_mul 3) |>.sub
      ((hS.logFirst hs.ne').const_mul 2)).div_const 5
  refine ⟨hR, ?_⟩
  change HasDerivAt (fun t => R t * H t) (R x * ((H x)^2 + logRadicalSecond (A x) (B x) (S x))) x
  convert hR.mul hH using 1
  ring

end Jet

/-- Replace just one of the parameters `(a,b,η)` by the variable of the slice. -/
def axisPoint (p : Row) (k : Fin 3) (x : ℝ) : Row := Function.update p k x

@[simp] theorem axisPoint_current (p : Row) (k : Fin 3) : axisPoint p k (p k) = p :=
  Function.update_eq_self k p

def axisSlope (k i : Fin 3) : ℝ := if i = k then 1 else 0

def directionSlope (k : Fin 3) : Row :=
  ![axisSlope k 0, axisSlope k 1, -axisSlope k 0 - axisSlope k 1]

def coordinateJet (k : Fin 3) (p : Row) (i : Fin 3) : Jet := ⟨p i, axisSlope k i, 0⟩

theorem coordinateJet_valid (p : Row) (k i : Fin 3) (x : ℝ) :
    Jet.ValidAt (fun t => coordinateJet k (axisPoint p k t) i) x := by
  by_cases h : i = k
  · subst i
    have hd : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
    simpa [Jet.ValidAt, coordinateJet, axisPoint, axisSlope] using
      And.intro hd (hasDerivAt_const x (1 : ℝ))
  · simpa only [Jet.ValidAt, coordinateJet, axisPoint, Function.update_of_ne h, axisSlope, ite_eq_right h] using
      And.intro (hasDerivAt_const x (p i)) (hasDerivAt_const x (0 : ℝ))

def directionJet (k : Fin 3) (p : Row) (i : Fin 3) : Jet :=
  ⟨parameterDirection (p 0) (p 1) i, directionSlope k i, 0⟩

theorem directionJet_valid (p : Row) (k i : Fin 3) (x : ℝ) :
    Jet.ValidAt (fun t => directionJet k (axisPoint p k t) i) x := by
  fin_cases i
  · exact coordinateJet_valid p k 0 x
  · exact coordinateJet_valid p k 1 x
  · change Jet.ValidAt (fun t => directionJet k (axisPoint p k t) (2 : Fin 3)) x
    have he (q : Row) : directionJet k q 2 =
        ((Jet.const 1).sub (coordinateJet k q 0)).sub (coordinateJet k q 1) := by
      simp [directionJet, parameterDirection, directionSlope, Jet.sub, Jet.const, coordinateJet]
    simpa only [he] using ((Jet.valid_const 1 x).sub (coordinateJet_valid p k 0 x)).sub
      (coordinateJet_valid p k 1 x)

/-- First and second derivatives of ε=η/(1+2η) in the checker’s three coordinate directions. -/
def depthJet (k : Fin 3) (p : Row) : Jet :=
  let n := 1 + 2 * p 2
  let t := axisSlope k 2
  ⟨p 2 / n, t / n^2, -4 * t / n^3⟩

private theorem axisSlope_sq (k i : Fin 3) : axisSlope k i ^ 2 = axisSlope k i := by
  by_cases h : i = k <;> simp [axisSlope, h]

theorem depthJet_valid (p : Row) (k : Fin 3) (x : ℝ) (hη : 0 ≤ axisPoint p k x 2) :
    Jet.ValidAt (fun t => depthJet k (axisPoint p k t)) x := by
  let f (t : ℝ) := axisPoint p k t 2
  let n (t : ℝ) := 1 + 2 * f t
  let b := axisSlope k 2
  have hf : HasDerivAt f b x := (coordinateJet_valid p k 2 x).1
  have hn : HasDerivAt n (2 * b) x := (hf.const_mul 2).const_add 1
  have hn₀ : n x ≠ 0 := by
    dsimp [n, f]
    positivity
  constructor
  · change HasDerivAt (fun t => f t / n t) (b / (n x)^2) x
    convert hf.div hn hn₀ using 1
    dsimp [n]
    field_simp [hn₀]
    ring
  · change HasDerivAt (fun t => b / (n t)^2) (-4 * b / (n x)^3) x
    have h := (hasDerivAt_const x b).div (hn.pow 2) (pow_ne_zero _ hn₀)
    convert h using 1
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply, zero_mul, zero_sub]
    have hb : b^2 = b := axisSlope_sq k 2
    field_simp [hn₀]
    ring_nf
    rw [hb]

/-- A, A′ and A″ in the order used by the radical interval calculation. -/
def radicalBaseJet (k : Fin 3) (p : Row) (j : Fin 3) : Jet :=
  let e := parameterDirection (p 0) (p 1)
  let v := directionSlope k
  let ε := depthJet k p
  let a := 1 - e j
  let c := cross e j
  let cp := v (j + 1) * e (j + 2) + e (j + 1) * v (j + 2)
  ⟨(1 - ε.value) * a + ε.value * c,
    -v j + ε.first * (c - a) + ε.value * (cp + v j),
    ε.second * (c - a) + 2 * ε.first * (cp + v j) + 2 * ε.value * v (j + 1) * v (j + 2)⟩

/-- B, B′ and B″ for the same component of the parameter direction. -/
def radicalOtherJet (k : Fin 3) (p : Row) (j : Fin 3) : Jet :=
  let e := parameterDirection (p 0) (p 1)
  let v := directionSlope k
  let ε := depthJet k p
  ⟨1 - ε.value * e j, -ε.first * e j - ε.value * v j,
    -ε.second * e j - 2 * ε.first * v j⟩

/-- The simplex identity gives σ′=−Σ eᵢvᵢ and σ″=−Σ vᵢ². -/
def radicalSigmaJet (k : Fin 3) (p : Row) : Jet :=
  let e := parameterDirection (p 0) (p 1)
  let v := directionSlope k
  ⟨sigmaTwo e, -(∑ i, e i * v i), -(∑ i, (v i)^2)⟩

theorem radicalBaseJet_valid (p : Row) (k j : Fin 3) (x : ℝ) (hη : 0 ≤ axisPoint p k x 2) :
    Jet.ValidAt (fun t => radicalBaseJet k (axisPoint p k t) j) x := by
  have hEq (q : Row) : radicalBaseJet k q j =
      (((Jet.const 1).sub (depthJet k q)).mul ((Jet.const 1).sub (directionJet k q j))).add
        ((depthJet k q).mul ((directionJet k q (j + 1)).mul (directionJet k q (j + 2)))) := by
    apply Jet.ext <;> simp only [radicalBaseJet, directionJet, cross, Jet.const, Jet.sub, Jet.add, Jet.mul] <;> ring
  have hε := depthJet_valid p k x hη
  have hd (i : Fin 3) := directionJet_valid p k i x
  have h1 := Jet.valid_const 1 x
  simpa only [hEq] using ((h1.sub hε).mul (h1.sub (hd j))).add (hε.mul ((hd (j + 1)).mul (hd (j + 2))))

theorem radicalOtherJet_valid (p : Row) (k j : Fin 3) (x : ℝ) (hη : 0 ≤ axisPoint p k x 2) :
    Jet.ValidAt (fun t => radicalOtherJet k (axisPoint p k t) j) x := by
  have hEq (q : Row) : radicalOtherJet k q j = (Jet.const 1).sub ((depthJet k q).mul (directionJet k q j)) := by
    apply Jet.ext <;> simp only [radicalOtherJet, directionJet, Jet.const, Jet.sub, Jet.mul] <;> ring
  simpa only [hEq] using (Jet.valid_const 1 x).sub ((depthJet_valid p k x hη).mul (directionJet_valid p k j x))

theorem radicalSigmaJet_valid (p : Row) (k : Fin 3) (x : ℝ) :
    Jet.ValidAt (fun t => radicalSigmaJet k (axisPoint p k t)) x := by
  have hEq (q : Row) : radicalSigmaJet k q =
      (((directionJet k q 0).mul (directionJet k q 1)).add ((directionJet k q 0).mul (directionJet k q 2))).add
        ((directionJet k q 1).mul (directionJet k q 2)) := by
    fin_cases k <;> apply Jet.ext <;>
      norm_num [radicalSigmaJet, directionJet, directionSlope, axisSlope, parameterDirection, sigmaTwo,
        Fin.sum_univ_three, Jet.add, Jet.mul]
  have h (i : Fin 3) := directionJet_valid p k i x
  simpa only [hEq] using (((h 0).mul (h 1)).add ((h 0).mul (h 2))).add ((h 1).mul (h 2))

def radicalJet (k : Fin 3) (p : Row) (j : Fin 3) : Jet :=
  Jet.radical (radicalBaseJet k p j) (radicalOtherJet k p j) (radicalSigmaJet k p)

@[simp] theorem radicalJet_value (k : Fin 3) (p : Row) (j : Fin 3) :
    (radicalJet k p j).value = radical (p 2 / (1 + 2 * p 2)) (parameterDirection (p 0) (p 1)) j := rfl

/-- Both derivatives are those of the actual chart radical along the selected parameter axis. -/
theorem radicalJet_validAt (p : Row) (k j : Fin 3) (x : ℝ) (hη : 0 ≤ axisPoint p k x 2)
    (ha : 0 < (radicalBaseJet k (axisPoint p k x) j).value)
    (hb : 0 < (radicalOtherJet k (axisPoint p k x) j).value)
    (hs : 0 < (radicalSigmaJet k (axisPoint p k x)).value) :
    Jet.ValidAt (fun t => radicalJet k (axisPoint p k t) j) x :=
  Jet.ValidAt.radical (radicalBaseJet_valid p k j x hη) (radicalOtherJet_valid p k j x hη)
    (radicalSigmaJet_valid p k x) ha hb hs

/-- Positive rational lower bounds discharge all divisors, even when `a=0` or `η=0`. -/
theorem ParameterCell.radicalJet_valid {c : ParameterCell} {a b η : ℝ} (ht : c.Contains a b η)
    (k j : Fin 3) (hη : 0 ≤ c.η.lo) (ha : 0 < (c.base j).lo) (hb : 0 < (c.other j).lo)
    (hs : 0 < c.sigma.lo) :
    let p : Row := ![a, b, η]
    Jet.ValidAt (fun x => radicalJet k (axisPoint p k x) j) (p k) := by
  intro p
  obtain ⟨hA, hB, hS⟩ := c.radical_factors_mem hη ht j
  have hη' : (0 : ℝ) ≤ η := (show (0 : ℝ) ≤ c.η.lo by exact_mod_cast hη).trans ht.eta.1
  have hA' : (0 : ℝ) < (radicalBaseJet k p j).value :=
    (show (0 : ℝ) < (c.base j).lo by exact_mod_cast ha).trans_le hA.1
  have hB' : (0 : ℝ) < (radicalOtherJet k p j).value :=
    (show (0 : ℝ) < (c.other j).lo by exact_mod_cast hb).trans_le hB.1
  have hS' : (0 : ℝ) < (radicalSigmaJet k p).value :=
    (show (0 : ℝ) < c.sigma.lo by exact_mod_cast hs).trans_le hS.1
  apply radicalJet_validAt p k j (p k) <;> rw [axisPoint_current]
  · exact hη'
  · exact hA'
  · exact hB'
  · exact hS'

end

end HlawkaSchatten.BelowExponent.Vertex
