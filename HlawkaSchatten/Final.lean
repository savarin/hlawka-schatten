/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.Variational
import HlawkaSchatten.MazurGapComparison

/-!
# Dimension-independent Hlawka constants for Schatten norms

This file removes the unit-sphere normalization from the variational
comparison and performs the final Hilbert-space Hlawka transfer.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Normalize a nonzero operator to the Schatten-`p` unit sphere.  The
definition is total; at zero it returns zero. -/
noncomputable def schattenNormalized (p : ℝ) (T : E →ₗ[ℂ] F) : E →ₗ[ℂ] F :=
  (((schattenPNorm p T)⁻¹ : ℝ) : ℂ) • T

theorem schattenPNorm_normalized {p : ℝ} (hp : 0 < p)
    {T : E →ₗ[ℂ] F} (hT : T ≠ 0) :
    schattenPNorm p (schattenNormalized p T) = 1 := by
  unfold schattenNormalized
  have hr : 0 < schattenPNorm p T := schattenPNorm_pos p hT
  rw [schattenPNorm_real_smul hp (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']

theorem singularValuePowerSum_normalized {p : ℝ} (hp : 0 < p)
    {T : E →ₗ[ℂ] F} (hT : T ≠ 0) :
    singularValuePowerSum p (schattenNormalized p T) = 1 :=
  (schattenPNorm_eq_one_iff hp _).mp (schattenPNorm_normalized hp hT)

theorem schattenPNorm_smul_normalized {p : ℝ} (_hp : 0 < p)
    {T : E →ₗ[ℂ] F} (hT : T ≠ 0) :
    ((schattenPNorm p T : ℝ) : ℂ) • schattenNormalized p T = T := by
  unfold schattenNormalized
  rw [smul_smul]
  have hr : 0 < schattenPNorm p T := schattenPNorm_pos p hT
  simp [hr.ne']

/-- The homogeneous rectangular Mazur map.  Unlike `rectangularMazurMap`,
this radial version preserves the Schatten norm rather than its power. -/
noncomputable def radialRectangularMazurMap
    (p : ℝ) (T : E →ₗ[ℂ] F) : E →ₗ[ℂ] F :=
  ((schattenPNorm p T : ℝ) : ℂ) •
    rectangularMazurMap p (schattenNormalized p T)

/-- Hilbert coordinates of the radial Mazur map. -/
noncomputable def radialMazurHilbertMap
    (p : ℝ) (T : E →ₗ[ℂ] F) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ E) => F) :=
  hilbertSchmidtCoordinates (stdOrthonormalBasis ℂ E)
    (radialRectangularMazurMap p T)

@[simp]
theorem radialRectangularMazurMap_zero {p : ℝ} (hp : 0 < p) :
    radialRectangularMazurMap p (0 : E →ₗ[ℂ] F) = 0 := by
  simp [radialRectangularMazurMap, schattenNormalized, schattenPNorm_zero p hp.ne']

@[simp]
theorem radialMazurHilbertMap_zero {p : ℝ} (hp : 0 < p) :
    radialMazurHilbertMap p (0 : E →ₗ[ℂ] F) = 0 := by
  unfold radialMazurHilbertMap
  rw [radialRectangularMazurMap_zero hp]
  exact map_zero (hilbertSchmidtLinearEquiv (stdOrthonormalBasis ℂ E))

/-- The radial Mazur map is an exact isometry on individual radii. -/
theorem norm_radialMazurHilbertMap {p : ℝ} (hp : 0 < p)
    (T : E →ₗ[ℂ] F) :
    ‖radialMazurHilbertMap p T‖ = schattenPNorm p T := by
  by_cases hT : T = 0
  · subst T
    simp [radialMazurHilbertMap_zero hp, schattenPNorm_zero p hp.ne']
  · have hr : 0 < schattenPNorm p T := schattenPNorm_pos p hT
    have hpow : singularValuePowerSum 2
        (rectangularMazurMap p (schattenNormalized p T)) = 1 := by
      rw [singularValuePowerSum_two_rectangularMazurMap hp]
      exact singularValuePowerSum_normalized hp hT
    have htwo : schattenPNorm 2
        (rectangularMazurMap p (schattenNormalized p T)) = 1 :=
      (schattenPNorm_eq_one_iff (by norm_num) _).mpr hpow
    unfold radialMazurHilbertMap radialRectangularMazurMap
    change ‖((schattenPNorm p T : ℝ) : ℂ) •
      hilbertSchmidtCoordinates (stdOrthonormalBasis ℂ E)
        (rectangularMazurMap p (schattenNormalized p T))‖ = schattenPNorm p T
    rw [norm_smul, ← schattenPNorm_two_eq_norm_hilbertSchmidtCoordinates,
      htwo, mul_one]
    simp [abs_of_pos hr]

/-- A nonzero operator, normalized as an element of the Schatten power
sphere. -/
noncomputable def schattenPowerDirection {p : ℝ} (hp : 0 < p)
    (T : E →ₗ[ℂ] F) (hT : T ≠ 0) :
    schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p :=
  ⟨schattenNormalized p T, singularValuePowerSum_normalized hp hT⟩

/-- Equation (7), with the unit-sphere normalization removed, for a finite
family of nonzero rectangular operators. -/
theorem finiteFamilyGap_two_sided
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p m M : ℝ} (hp : 1 < p) (hm : 0 ≤ m)
    (x : ι → E →ₗ[ℂ] F) (hx : ∀ i, x i ≠ 0)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    2 * m * ((∑ i, schattenPNorm p (x i)) - schattenPNorm 2
        (∑ i, radialRectangularMazurMap p (x i))) ≤
        (∑ i, schattenPNorm p (x i)) - schattenPNorm p (∑ i, x i) ∧
      (∑ i, schattenPNorm p (x i)) - schattenPNorm p (∑ i, x i) ≤
        2 * M * ((∑ i, schattenPNorm p (x i)) - schattenPNorm 2
          (∑ i, radialRectangularMazurMap p (x i))) := by
  let a : ι → ℝ := fun i => schattenPNorm p (x i)
  let u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p :=
    fun i => schattenPowerDirection (zero_lt_one.trans hp) (x i) (hx i)
  have ha : ∀ i, 0 ≤ a i := fun i => schattenPNorm_nonneg p (x i)
  have hweighted : rectangularWeightedSum a u = ∑ i, x i := by
    unfold rectangularWeightedSum
    apply Finset.sum_congr rfl
    intro i _
    exact schattenPNorm_smul_normalized (zero_lt_one.trans hp) (hx i)
  have hbarycenter : rectangularMazurBarycenter p a u =
      ∑ i, radialRectangularMazurMap p (x i) := by
    unfold rectangularMazurBarycenter radialRectangularMazurMap
    rfl
  have h := rectangularVariationalGap_two_sided
    (stdOrthonormalBasis ℂ E) hp hm a ha u hbound
  rw [hweighted, hbarycenter] at h
  exact h

/-- The two-operator specialization of the unnormalized variational gap. -/
theorem pairGap_radial_two_sided_of_ne
    {p m M : ℝ} (hp : 1 < p) (hm : 0 ≤ m)
    (x y : E →ₗ[ℂ] F) (hx : x ≠ 0) (hy : y ≠ 0)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    2 * m * mappedPairGap (schattenPNorm p) (radialMazurHilbertMap p) x y ≤
        pairGap (schattenPNorm p) x y ∧
      pairGap (schattenPNorm p) x y ≤
        2 * M * mappedPairGap (schattenPNorm p) (radialMazurHilbertMap p) x y := by
  have h := finiteFamilyGap_two_sided hp hm (![x, y] : Fin 2 → E →ₗ[ℂ] F)
    (by intro i; fin_cases i <;> assumption) hbound
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Fin.isValue] at h
  dsimp only [pairGap, mappedPairGap, radialMazurHilbertMap]
  simpa only [← hilbertSchmidtCoordinates_add,
    ← schattenPNorm_two_eq_norm_hilbertSchmidtCoordinates] using h

/-- The three-operator specialization of the unnormalized variational gap. -/
theorem tripleGap_radial_two_sided_of_ne
    {p m M : ℝ} (hp : 1 < p) (hm : 0 ≤ m)
    (x y z : E →ₗ[ℂ] F) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    2 * m * mappedTripleGap (schattenPNorm p) (radialMazurHilbertMap p) x y z ≤
        tripleGap (schattenPNorm p) x y z ∧
      tripleGap (schattenPNorm p) x y z ≤
        2 * M * mappedTripleGap (schattenPNorm p) (radialMazurHilbertMap p) x y z := by
  have h := finiteFamilyGap_two_sided hp hm
    (![x, y, z] : Fin 3 → E →ₗ[ℂ] F)
    (by intro i; fin_cases i <;> assumption) hbound
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue] at h
  dsimp only [tripleGap, mappedTripleGap, radialMazurHilbertMap]
  simpa only [← hilbertSchmidtCoordinates_add,
    ← schattenPNorm_two_eq_norm_hilbertSchmidtCoordinates, add_assoc] using h

/-- The two-sided pair comparison also holds when one or both inputs vanish. -/
theorem pairGap_radial_two_sided
    {p m M : ℝ} (hp : 1 < p) (hm : 0 ≤ m)
    (x y : E →ₗ[ℂ] F)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    2 * m * mappedPairGap (schattenPNorm p) (radialMazurHilbertMap p) x y ≤
        pairGap (schattenPNorm p) x y ∧
      pairGap (schattenPNorm p) x y ≤
        2 * M * mappedPairGap (schattenPNorm p) (radialMazurHilbertMap p) x y := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  by_cases hx : x = 0
  · subst x
    have hgap : pairGap (schattenPNorm p) (0 : E →ₗ[ℂ] F) y = 0 := by
      simp [pairGap, schattenPNorm_zero p hp0.ne']
    have hmapped : mappedPairGap (schattenPNorm p) (radialMazurHilbertMap p)
        (0 : E →ₗ[ℂ] F) y = 0 := by
      simp [mappedPairGap, schattenPNorm_zero p hp0.ne',
        radialMazurHilbertMap_zero hp0, norm_radialMazurHilbertMap hp0]
    rw [hgap, hmapped]
    simp
  · by_cases hy : y = 0
    · subst y
      have hgap : pairGap (schattenPNorm p) x (0 : E →ₗ[ℂ] F) = 0 := by
        simp [pairGap, schattenPNorm_zero p hp0.ne']
      have hmapped : mappedPairGap (schattenPNorm p) (radialMazurHilbertMap p)
          x (0 : E →ₗ[ℂ] F) = 0 := by
        simp [mappedPairGap, schattenPNorm_zero p hp0.ne',
          radialMazurHilbertMap_zero hp0, norm_radialMazurHilbertMap hp0]
      rw [hgap, hmapped]
      simp
    · exact pairGap_radial_two_sided_of_ne hp hm x y hx hy hbound

/-- The upper three-body comparison, including all zero-input cases. -/
theorem tripleGap_radial_le
    {p m M : ℝ} (hp : 1 < p) (hm : 0 ≤ m)
    (x y z : E →ₗ[ℂ] F)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    tripleGap (schattenPNorm p) x y z ≤
      2 * M * mappedTripleGap (schattenPNorm p) (radialMazurHilbertMap p) x y z := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  by_cases hx : x = 0
  · subst x
    have h := (pairGap_radial_two_sided hp hm y z hbound).2
    simpa [tripleGap, mappedTripleGap, pairGap, mappedPairGap,
      schattenPNorm_zero p hp0.ne', radialMazurHilbertMap_zero hp0] using h
  · by_cases hy : y = 0
    · subst y
      have h := (pairGap_radial_two_sided hp hm x z hbound).2
      simpa [tripleGap, mappedTripleGap, pairGap, mappedPairGap,
        schattenPNorm_zero p hp0.ne', radialMazurHilbertMap_zero hp0] using h
    · by_cases hz : z = 0
      · subst z
        have h := (pairGap_radial_two_sided hp hm x y hbound).2
        simpa [tripleGap, mappedTripleGap, pairGap, mappedPairGap,
          schattenPNorm_zero p hp0.ne', radialMazurHilbertMap_zero hp0] using h
      · exact (tripleGap_radial_two_sided_of_ne hp hm x y z hx hy hz hbound).2

/-- For each `1 < p`, the scalar Bregman ratio supplies one finite Hlawka
constant `M / m` which works in every pair of finite complex Hilbert
spaces.  In particular, it is independent of both matrix dimensions. -/
theorem exists_uniform_schattenPNorm_hlawkaConstant
    {p : ℝ} (hp : 1 < p) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ {G K : Type*}
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K],
        HasHlawkaConstant
          (schattenPNorm p : (G →ₗ[ℂ] K) → ℝ) (M / m) := by
  obtain ⟨m, M, hm, hmM, hbound⟩ :=
    exists_uniform_dilatedBregmanTrace_two_sided hp
  refine ⟨m, M, hm, hmM, ?_⟩
  intro G K _ _ _ _ _ _
  apply hasHlawkaConstant_of_mappedGapComparison (𝕜 := ℂ)
    (schattenPNorm p : (G →ₗ[ℂ] K) → ℝ)
    (schattenPNorm p : (G →ₗ[ℂ] K) → ℝ)
    (radialMazurHilbertMap p) m M hm (hm.le.trans hmM)
  · exact norm_radialMazurHilbertMap (zero_lt_one.trans hp)
  · intro x y z
    exact tripleGap_radial_le hp hm.le x y z (fun S T => hbound S T)
  · intro x y
    exact (pairGap_radial_two_sided hp hm.le x y (fun S T => hbound S T)).1

/-- Dimension-independent existence, with the ratio representation hidden. -/
theorem exists_dimensionIndependent_schattenPNorm_hlawkaConstant
    {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {G K : Type*}
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K],
        HasHlawkaConstant (schattenPNorm p : (G →ₗ[ℂ] K) → ℝ) C := by
  obtain ⟨m, M, hm, hmM, h⟩ := exists_uniform_schattenPNorm_hlawkaConstant hp
  exact ⟨M / m, div_nonneg (hm.le.trans hmM) hm.le, h⟩

end HlawkaSchatten
