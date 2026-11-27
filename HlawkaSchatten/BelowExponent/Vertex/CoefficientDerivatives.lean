/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Vertex.RadicalDerivatives

/-! Real first and second derivatives of the normalized vertex coefficients. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent.Vertex

noncomputable section

namespace Jet

def scale (r : ℝ) (f : Jet) : Jet := ⟨r * f.value, r * f.first, r * f.second⟩

theorem ValidAt.scale {f : ℝ → Jet} {t : ℝ} (hf : ValidAt f t) (r : ℝ) :
    ValidAt (fun x => scale r (f x)) t :=
  ⟨hf.1.const_mul r, hf.2.const_mul r⟩

def sumThree (f : Fin 3 → Jet) : Jet := ((f 0).add (f 1)).add (f 2)

theorem valid_sumThree {f : ℝ → Fin 3 → Jet} {t : ℝ} (h : ∀ i, ValidAt (fun x => f x i) t) :
    ValidAt (fun x => sumThree (f x)) t := ((h 0).add (h 1)).add (h 2)

@[simp] theorem sumThree_value (f : Fin 3 → Jet) : (sumThree f).value = ∑ i, (f i).value := by
  simp [sumThree, add, Fin.sum_univ_three]

/-- The quotient derivative written in terms of the value and first derivative of the quotient. -/
def div (num den : Jet) : Jet :=
  let v := num.value / den.value
  let v' := (num.first - v * den.first) / den.value
  ⟨v, v', (num.second - v * den.second - 2 * v' * den.first) / den.value⟩

private theorem hasDerivAt_div_value {f g : ℝ → ℝ} {x a b : ℝ} (hf : HasDerivAt f a x)
    (hg : HasDerivAt g b x) (h : g x ≠ 0) :
    HasDerivAt (fun t => f t / g t) ((a - (f x / g x) * b) / g x) x := by
  convert hf.div hg h using 1
  field_simp [h]

theorem ValidAt.div {f g : ℝ → Jet} {x : ℝ} (hf : ValidAt f x) (hg : ValidAt g x)
    (hg₀ : (g x).value ≠ 0) : ValidAt (fun t => (f t).div (g t)) x := by
  let v (t : ℝ) := (f t).value / (g t).value
  let v' (t : ℝ) := ((f t).first - v t * (g t).first) / (g t).value
  have Hv : HasDerivAt v (v' x) x := hasDerivAt_div_value hf.1 hg.1 hg₀
  have Hn := hf.2.sub (Hv.mul hg.2)
  have Hd := hasDerivAt_div_value Hn hg.1 hg₀
  refine ⟨Hv, ?_⟩
  change HasDerivAt v' (((f x).second - v x * (g x).second - 2 * v' x * (g x).first) / (g x).value) x
  convert Hd using 1
  change _ = ((f x).second - (v' x * (g x).first + v x * (g x).second) - v' x * (g x).first) / (g x).value
  ring

end Jet

/-- The η ratio used in the beta weights, together with its parameter derivatives. -/
def etaRatioJet (k : Fin 3) (p : Row) : Jet :=
  let η := coordinateJet k p 2
  η.div ((Jet.const 1).add η)

theorem etaRatioJet_valid (p : Row) (k : Fin 3) (x : ℝ) (hη : 0 ≤ axisPoint p k x 2) :
    Jet.ValidAt (fun t => etaRatioJet k (axisPoint p k t)) x := by
  have h := coordinateJet_valid p k 2 x
  refine h.div ((Jet.valid_const 1 x).add h) ?_
  change 1 + axisPoint p k x 2 ≠ 0
  linarith only [hη]

/-- The compact η ratio formulas used in the interval preparer. -/
theorem etaRatioJet_eq (k : Fin 3) (p : Row) (hη : 0 ≤ p 2) :
    let f := 1 + p 2
    let t := axisSlope k 2
    etaRatioJet k p = ⟨p 2 / f, t / f^2, -2 * t / (f^2 * f)⟩ := by
  intro f t
  have hf : f ≠ 0 := by dsimp [f]; linarith only [hη]
  have ht : t^2 = t := by dsimp [t, axisSlope]; split <;> norm_num
  have ht' : t * t = t := by simpa only [pow_two] using ht
  have hd : (t - (p 2 / f) * t) / f = t / f^2 := by
    field_simp [hf]
    dsimp [f]
    ring
  apply Jet.ext
  · rfl
  · simpa only [etaRatioJet, Jet.div, Jet.add, Jet.const, coordinateJet, zero_add] using hd
  · change (0 - (p 2 / f) * (0 + 0) - 2 * ((t - (p 2 / f) * (0 + t)) / f) * (0 + t)) / f =
      -2 * t / (f^2 * f)
    simp only [zero_add, mul_zero, sub_zero, hd]
    field_simp [hf]
    nlinarith only [ht']

def betaCoordinateJet (k : Fin 3) (p : Row) (i : Fin 4) : Jet :=
  let e := directionJet k p
  ![Jet.const 1, (e 0).div (e 1), (e 0).div (e 2), (e 0).mul (etaRatioJet k p)] i

def betaNumeratorJet (k : Fin 3) (p : Row) (i : Fin 4) : Jet :=
  let v := betaCoordinateJet k p i
  v.mul v

def betaDenJet (k : Fin 3) (p : Row) : Jet :=
  let n := betaNumeratorJet k p
  (((n 0).add (n 1)).add (n 2)).add (n 3)

def betaJet (k : Fin 3) (p : Row) (j : Fin 3) : Jet :=
  (betaNumeratorJet k p j.castSucc).div (betaDenJet k p)

def betaHeavyNumeratorJet (k : Fin 3) (p : Row) : Jet :=
  let v := (directionJet k p 0).mul ((Jet.const 1).add (etaRatioJet k p))
  v.mul v

def betaHeavyJet (k : Fin 3) (p : Row) : Jet :=
  (betaHeavyNumeratorJet k p).div (betaDenJet k p)

@[simp] theorem betaDenJet_value (k : Fin 3) (p : Row) :
    (betaDenJet k p).value = betaDen (p 2) (parameterDirection (p 0) (p 1)) := by
  simp [betaDenJet, betaNumeratorJet, betaCoordinateJet, etaRatioJet, betaDen, Jet.add, Jet.mul,
    Jet.div, Jet.const, coordinateJet, directionJet, pow_two]

@[simp] theorem betaJet_value (k : Fin 3) (p : Row) (j : Fin 3) :
    (betaJet k p j).value = beta (p 2) (parameterDirection (p 0) (p 1)) j := by
  fin_cases j <;> simp [betaJet, betaNumeratorJet, betaCoordinateJet, beta, betaNumer, directionJet,
    Jet.div, Jet.mul, Jet.const, pow_two, Fin.castSucc]

@[simp] theorem betaHeavyJet_value (k : Fin 3) (p : Row) :
    (betaHeavyJet k p).value = betaHeavy (p 2) (parameterDirection (p 0) (p 1)) := by
  simp [betaHeavyJet, betaHeavyNumeratorJet, betaHeavy, directionJet, etaRatioJet, coordinateJet,
    Jet.div, Jet.mul, Jet.const, Jet.add, pow_two]

private theorem betaNumeratorJet_valid (p : Row) (k : Fin 3) (i : Fin 4) (x : ℝ)
    (hη : 0 ≤ axisPoint p k x 2) (h₁ : (directionJet k (axisPoint p k x) 1).value ≠ 0)
    (h₂ : (directionJet k (axisPoint p k x) 2).value ≠ 0) :
    Jet.ValidAt (fun t => betaNumeratorJet k (axisPoint p k t) i) x := by
  have he (j : Fin 3) := directionJet_valid p k j x
  have hβ : Jet.ValidAt (fun t => betaCoordinateJet k (axisPoint p k t) i) x := by
    fin_cases i
    · exact Jet.valid_const 1 x
    · exact (he 0).div (he 1) h₁
    · exact (he 0).div (he 2) h₂
    · exact (he 0).mul (etaRatioJet_valid p k x hη)
  exact hβ.mul hβ

private theorem betaDenJet_valid (p : Row) (k : Fin 3) (x : ℝ) (hη : 0 ≤ axisPoint p k x 2)
    (h₁ : (directionJet k (axisPoint p k x) 1).value ≠ 0)
    (h₂ : (directionJet k (axisPoint p k x) 2).value ≠ 0) :
    Jet.ValidAt (fun t => betaDenJet k (axisPoint p k t)) x := by
  have h i := betaNumeratorJet_valid p k i x hη h₁ h₂
  exact (((h 0).add (h 1)).add (h 2)).add (h 3)

private theorem betaDenJet_pos (k : Fin 3) (p : Row) : 0 < (betaDenJet k p).value := by
  rw [betaDenJet_value]
  unfold betaDen
  positivity

theorem betaJet_validAt (p : Row) (k j : Fin 3) (x : ℝ) (hη : 0 ≤ axisPoint p k x 2)
    (h₁ : (directionJet k (axisPoint p k x) 1).value ≠ 0)
    (h₂ : (directionJet k (axisPoint p k x) 2).value ≠ 0) :
    Jet.ValidAt (fun t => betaJet k (axisPoint p k t) j) x :=
  (betaNumeratorJet_valid p k j.castSucc x hη h₁ h₂).div (betaDenJet_valid p k x hη h₁ h₂)
    (betaDenJet_pos k (axisPoint p k x)).ne'

theorem betaHeavyJet_validAt (p : Row) (k : Fin 3) (x : ℝ) (hη : 0 ≤ axisPoint p k x 2)
    (h₁ : (directionJet k (axisPoint p k x) 1).value ≠ 0)
    (h₂ : (directionJet k (axisPoint p k x) 2).value ≠ 0) :
    Jet.ValidAt (fun t => betaHeavyJet k (axisPoint p k t)) x := by
  have h := (directionJet_valid p k 0 x).mul ((Jet.valid_const 1 x).add (etaRatioJet_valid p k x hη))
  exact (h.mul h).div (betaDenJet_valid p k x hη h₁ h₂) (betaDenJet_pos k (axisPoint p k x)).ne'

def complementJet (k : Fin 3) (p : Row) (i : Fin 3) : Jet :=
  (Jet.const 1).sub (directionJet k p i)

@[simp] theorem complementJet_value (k : Fin 3) (p : Row) (i : Fin 3) :
    (complementJet k p i).value = 1 - parameterDirection (p 0) (p 1) i := rfl

def signedRadicalJet (k : Fin 3) (p : Row) (j : Fin 3) : Jet :=
  Jet.sumThree (fun i => Jet.scale (if i = j then -1 else 1) (radicalJet k p i))

@[simp] theorem signedRadicalJet_value (k : Fin 3) (p : Row) (j : Fin 3) :
    let R := radical (p 2 / (1 + 2 * p 2)) (parameterDirection (p 0) (p 1))
    (signedRadicalJet k p j).value = (∑ i, R i) - 2 * R j := by
  intro R
  fin_cases j <;> norm_num [signedRadicalJet, Jet.scale, Fin.sum_univ_three, R] <;> ring

private theorem signedRadicalJet_valid (p : Row) (k j : Fin 3) (x : ℝ)
    (hR : ∀ i, Jet.ValidAt (fun t => radicalJet k (axisPoint p k t) i) x) :
    Jet.ValidAt (fun t => signedRadicalJet k (axisPoint p k t) j) x :=
  Jet.valid_sumThree (fun i => (hR i).scale (if i = j then -1 else 1))

/-- The term X shared by the three normalized coefficients. The signed radical sum avoids
subtracting two correlated interval occurrences of the same radical. -/
def sharedCoefficientJet (k : Fin 3) (p : Row) : Jet :=
  let ε := depthJet k p
  let bh := betaHeavyJet k p
  let T := Jet.sumThree (radicalJet k p)
  let first := (((ε.mul bh).mul ((Jet.const 1).sub ε)).mul (T.sub ε))
  let next := fun i => ((betaJet k p i).mul (directionJet k p i)).mul (ε.add (signedRadicalJet k p i))
  (Jet.scale (2 / 3) first).add (Jet.sumThree (fun i => Jet.scale (2 / 3) (next i)))

/-- The normalized coefficient d and its two derivatives from the exact chart. -/
def parameterDJet (k : Fin 3) (p : Row) (j : Fin 3) : Jet :=
  let ε := depthJet k p
  let A := complementJet k p j
  let b := betaJet k p
  let R := radicalJet k p
  let M := (Jet.const 1).sub (ε.mul A)
  let first := M.mul ((Jet.const 1).sub (Jet.scale 2 (b j)))
  let second := A.mul (signedRadicalJet k p j)
  let third := Jet.scale (-2) (((ε.mul (betaHeavyJet k p)).mul (R j)).mul M)
  let fourth := Jet.scale (-2) (A.mul (((b (j + 1)).mul (R (j + 2))).add ((b (j + 2)).mul (R (j + 1)))))
  (((first.add second).add third).add fourth).add (sharedCoefficientJet k p)

def normalizerJet (k : Fin 3) (p : Row) : Jet :=
  (Jet.const 1).add (Jet.scale 2 (coordinateJet k p 2))

def parameterWeightJet (k : Fin 3) (p : Row) (j : Fin 3) : Jet :=
  ((normalizerJet k p).mul (radicalJet k p j)).add ((coordinateJet k p 2).mul (parameterDJet k p j))

/-- The coefficient hᵢⱼ in `linearFeature`, including its two parameter derivatives. -/
def parameterHJet (k : Fin 3) (p : Row) (i j : Fin 3) : Jet :=
  (complementJet k p i).mul (parameterWeightJet k p j)

private theorem depthJet_value (k : Fin 3) (p : Row) : (depthJet k p).value = p 2 / (1 + 2 * p 2) := rfl

@[simp] theorem parameterDJet_value (k : Fin 3) (p : Row) (j : Fin 3) :
    (parameterDJet k p j).value = parameterD (p 0) (p 1) (p 2) j := by
  simp [parameterDJet, sharedCoefficientJet, parameterD, coefficient, Jet.add, Jet.sub, Jet.mul, Jet.scale,
    Jet.const, depthJet_value, directionJet, Fin.sum_univ_three]
  ring

@[simp] theorem parameterWeightJet_value (k : Fin 3) (p : Row) (j : Fin 3) :
    (parameterWeightJet k p j).value = parameterWeight (p 0) (p 1) (p 2) j := by
  simp [parameterWeightJet, normalizerJet, coordinateJet, Jet.add, Jet.mul, Jet.scale, Jet.const,
    parameterWeight, rowWeight]

@[simp] theorem parameterHJet_value (k : Fin 3) (p : Row) (i j : Fin 3) :
    (parameterHJet k p i j).value = (1 - parameterDirection (p 0) (p 1) i) * parameterWeight (p 0) (p 1) (p 2) j := by
  simp [parameterHJet, Jet.mul]

private theorem complementJet_valid (p : Row) (k i : Fin 3) (x : ℝ) :
    Jet.ValidAt (fun t => complementJet k (axisPoint p k t) i) x :=
  (Jet.valid_const 1 x).sub (directionJet_valid p k i x)

private theorem sharedCoefficientJet_valid (p : Row) (k : Fin 3) (x : ℝ) (hη : 0 ≤ axisPoint p k x 2)
    (h₁ : (directionJet k (axisPoint p k x) 1).value ≠ 0)
    (h₂ : (directionJet k (axisPoint p k x) 2).value ≠ 0)
    (hR : ∀ i, Jet.ValidAt (fun t => radicalJet k (axisPoint p k t) i) x) :
    Jet.ValidAt (fun t => sharedCoefficientJet k (axisPoint p k t)) x := by
  have hε := depthJet_valid p k x hη
  have hh := betaHeavyJet_validAt p k x hη h₁ h₂
  have hT := Jet.valid_sumThree hR
  have hf := (((hε.mul hh).mul ((Jet.valid_const 1 x).sub hε)).mul (hT.sub hε)).scale (2 / 3)
  have ho := Jet.valid_sumThree (fun i =>
    (((betaJet_validAt p k i x hη h₁ h₂).mul (directionJet_valid p k i x)).mul
      (hε.add (signedRadicalJet_valid p k i x hR))).scale (2 / 3))
  exact hf.add ho

theorem parameterDJet_validAt (p : Row) (k j : Fin 3) (x : ℝ) (hη : 0 ≤ axisPoint p k x 2)
    (h₁ : (directionJet k (axisPoint p k x) 1).value ≠ 0)
    (h₂ : (directionJet k (axisPoint p k x) 2).value ≠ 0)
    (hR : ∀ i, Jet.ValidAt (fun t => radicalJet k (axisPoint p k t) i) x) :
    Jet.ValidAt (fun t => parameterDJet k (axisPoint p k t) j) x := by
  have hε := depthJet_valid p k x hη
  have ha := complementJet_valid p k j x
  have hb (i : Fin 3) := betaJet_validAt p k i x hη h₁ h₂
  have hbh := betaHeavyJet_validAt p k x hη h₁ h₂
  have hm := (Jet.valid_const 1 x).sub (hε.mul ha)
  have hfirst := hm.mul ((Jet.valid_const 1 x).sub ((hb j).scale 2))
  have hsecond := ha.mul (signedRadicalJet_valid p k j x hR)
  have hthird := (((hε.mul hbh).mul (hR j)).mul hm).scale (-2)
  have hfourth := (ha.mul (((hb (j + 1)).mul (hR (j + 2))).add ((hb (j + 2)).mul (hR (j + 1))))).scale (-2)
  exact (((hfirst.add hsecond).add hthird).add hfourth).add (sharedCoefficientJet_valid p k x hη h₁ h₂ hR)

theorem parameterWeightJet_validAt (p : Row) (k j : Fin 3) (x : ℝ) (hη : 0 ≤ axisPoint p k x 2)
    (h₁ : (directionJet k (axisPoint p k x) 1).value ≠ 0)
    (h₂ : (directionJet k (axisPoint p k x) 2).value ≠ 0)
    (hR : ∀ i, Jet.ValidAt (fun t => radicalJet k (axisPoint p k t) i) x) :
    Jet.ValidAt (fun t => parameterWeightJet k (axisPoint p k t) j) x := by
  have hh := coordinateJet_valid p k 2 x
  have hn := (Jet.valid_const 1 x).add (hh.scale 2)
  exact (hn.mul (hR j)).add (hh.mul (parameterDJet_validAt p k j x hη h₁ h₂ hR))

theorem parameterHJet_validAt (p : Row) (k i j : Fin 3) (x : ℝ) (hη : 0 ≤ axisPoint p k x 2)
    (h₁ : (directionJet k (axisPoint p k x) 1).value ≠ 0)
    (h₂ : (directionJet k (axisPoint p k x) 2).value ≠ 0)
    (hR : ∀ i, Jet.ValidAt (fun t => radicalJet k (axisPoint p k t) i) x) :
    Jet.ValidAt (fun t => parameterHJet k (axisPoint p k t) i j) x :=
  (complementJet_valid p k i x).mul (parameterWeightJet_validAt p k j x hη h₁ h₂ hR)

/-- The coefficient derivatives on an actual parameter box use its rational lower bounds. -/
theorem ParameterCell.coefficientJets_valid {c : ParameterCell} {a b η : ℝ} (ht : c.Contains a b η)
    (k : Fin 3) (hη : 0 ≤ c.η.lo) (h₁ : 0 < (c.direction 1).lo) (h₂ : 0 < (c.direction 2).lo)
    (hA : ∀ j, 0 < (c.base j).lo) (hB : ∀ j, 0 < (c.other j).lo) (hS : 0 < c.sigma.lo) :
    let p : Row := ![a, b, η]
    (∀ j, Jet.ValidAt (fun x => parameterDJet k (axisPoint p k x) j) (p k)) ∧
      (∀ i j, Jet.ValidAt (fun x => parameterHJet k (axisPoint p k x) i j) (p k)) := by
  intro p
  have hη' : 0 ≤ axisPoint p k (p k) 2 := by
    rw [axisPoint_current]
    exact (show (0 : ℝ) ≤ c.η.lo by exact_mod_cast hη).trans ht.eta.1
  have hpositive (i : Fin 3) (h : 0 < (c.direction i).lo) :
      (directionJet k (axisPoint p k (p k)) i).value ≠ 0 := by
    rw [axisPoint_current]
    exact ((show (0 : ℝ) < (c.direction i).lo by exact_mod_cast h).trans_le
      (ParameterCell.direction_mem ht i).1).ne'
  have hR (j : Fin 3) := ParameterCell.radicalJet_valid ht k j hη (hA j) (hB j) hS
  exact ⟨fun j => parameterDJet_validAt p k j _ hη' (hpositive 1 h₁) (hpositive 2 h₂) hR,
    fun i j => parameterHJet_validAt p k i j _ hη' (hpositive 1 h₁) (hpositive 2 h₂) hR⟩

end

end HlawkaSchatten.BelowExponent.Vertex
