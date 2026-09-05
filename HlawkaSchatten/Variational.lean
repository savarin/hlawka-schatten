/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import HlawkaSchatten.HilbertSchmidt
import HlawkaSchatten.HermitianDilation

/-!
# Variational minima for the Bregman--Mazur argument

This file proves two reusable parts of the variational layer.  First, a
pointwise two-sided comparison transports to attained global minima, even
when the two objectives are indexed by different but equivalent spheres.
Second, the weighted squared-distance objective on a Hilbert unit sphere has
the exact minimum used in the Schatten argument.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace ComplexConjugate

/-- `value` is an attained global minimum of `f`. -/
def IsGlobalMinimumValue {A : Type*} (f : A → ℝ) (value : ℝ) : Prop :=
  (∀ x, value ≤ f x) ∧ ∃ x, f x = value

/-- Global minimum values are unchanged by reparametrizing the domain by an
equivalence. -/
theorem isGlobalMinimumValue_comp_equiv
    {A B : Type*} (e : A ≃ B) (f : B → ℝ) (value : ℝ) :
    IsGlobalMinimumValue (f ∘ e) value ↔ IsGlobalMinimumValue f value := by
  constructor
  · rintro ⟨hlower, ⟨x, hx⟩⟩
    refine ⟨fun y ↦ ?_, ⟨e x, hx⟩⟩
    simpa only [Function.comp_apply, e.apply_symm_apply] using hlower (e.symm y)
  · rintro ⟨hlower, ⟨y, hy⟩⟩
    refine ⟨fun x ↦ hlower (e x), ⟨e.symm y, ?_⟩⟩
    simpa only [Function.comp_apply, e.apply_symm_apply] using hy

/-- A pointwise two-sided comparison yields the same comparison between
attained global minima.  The equivalence permits the two objectives to live
on different presentations of the same sphere. -/
theorem globalMinimumValue_two_sided_of_equiv
    {A B : Type*} (e : A ≃ B) (f : A → ℝ) (g : B → ℝ)
    (fmin gmin m M : ℝ) (hm : 0 ≤ m)
    (hf : IsGlobalMinimumValue f fmin)
    (hg : IsGlobalMinimumValue g gmin)
    (hcompare : ∀ x, m * g (e x) ≤ f x ∧ f x ≤ M * g (e x)) :
    m * gmin ≤ fmin ∧ fmin ≤ M * gmin := by
  constructor
  · obtain ⟨x, hx⟩ := hf.2
    calc
      m * gmin ≤ m * g (e x) := mul_le_mul_of_nonneg_left (hg.1 (e x)) hm
      _ ≤ f x := (hcompare x).1
      _ = fmin := hx
  · obtain ⟨y, hy⟩ := hg.2
    calc
      fmin ≤ f (e.symm y) := hf.1 (e.symm y)
      _ ≤ M * g (e (e.symm y)) := (hcompare (e.symm y)).2
      _ = M * gmin := by rw [e.apply_symm_apply, hy]

variable {𝕜 H ι : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Real-weighted sum of a finite family in a real or complex inner-product
space. -/
noncomputable def weightedHilbertSum (a : ι → ℝ) (u : ι → H) : H :=
  ∑ i, (a i : 𝕜) • u i

/-- Weighted squared-distance objective used in the Hilbert variational
identity. -/
noncomputable def weightedHilbertObjective
    (a : ι → ℝ) (u : ι → H) (v : H) : ℝ :=
  ∑ i, a i * ‖u i - v‖ ^ 2

/-- On unit vectors, the weighted squared-distance objective is affine in
the real part of the inner product with the weighted sum. -/
theorem weightedHilbertObjective_eq
    (a : ι → ℝ) (u : ι → H) (v : H)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ‖v‖ = 1) :
    weightedHilbertObjective a u v =
      2 * (∑ i, a i -
        RCLike.re ⟪weightedHilbertSum (𝕜 := 𝕜) a u, v⟫_𝕜) := by
  unfold weightedHilbertObjective weightedHilbertSum
  simp_rw [norm_sub_sq (𝕜 := 𝕜), hu, hv, one_pow]
  rw [sum_inner, map_sum]
  simp only [inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul]
  have hterm : ∀ i, a i * (1 - 2 * RCLike.re ⟪u i, v⟫_𝕜 + 1) =
      2 * a i - 2 * (a i * RCLike.re ⟪u i, v⟫_𝕜) := by
    intro i
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Exact Hilbert unit-sphere minimum:

`min_{‖v‖=1} ∑ i, aᵢ ‖uᵢ-v‖² = 2 (∑ i, aᵢ - ‖∑ i aᵢuᵢ‖)`.

The nonempty-index assumption supplies a unit vector in the zero weighted-sum
case.  No sign hypothesis on the weights is needed for the identity. -/
theorem weightedHilbertObjective_isGlobalMinimumValue
    [Nonempty ι] (a : ι → ℝ) (u : ι → H)
    (hu : ∀ i, ‖u i‖ = 1) :
    IsGlobalMinimumValue
      (fun v : unitSphere H ↦ weightedHilbertObjective a u v.1)
      (2 * (∑ i, a i - ‖weightedHilbertSum (𝕜 := 𝕜) a u‖)) := by
  let w := weightedHilbertSum (𝕜 := 𝕜) a u
  constructor
  · intro v
    change 2 * (∑ i, a i - ‖w‖) ≤ weightedHilbertObjective a u v.1
    rw [weightedHilbertObjective_eq (𝕜 := 𝕜) a u v.1 hu v.property]
    have hinner := re_inner_le_norm (𝕜 := 𝕜) w v.1
    rw [v.property, mul_one] at hinner
    linarith
  · by_cases hw : w = 0
    · let i : ι := Classical.choice inferInstance
      refine ⟨⟨u i, hu i⟩, ?_⟩
      change weightedHilbertObjective a u (u i) =
        2 * (∑ j, a j - ‖w‖)
      rw [weightedHilbertObjective_eq (𝕜 := 𝕜) a u (u i) hu (hu i)]
      change 2 * (∑ j, a j - RCLike.re ⟪w, u i⟫_𝕜) =
        2 * (∑ j, a j - ‖w‖)
      rw [hw, inner_zero_left, map_zero, norm_zero]
    · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
      let v : H := ((‖w‖⁻¹ : ℝ) : 𝕜) • w
      have hv : ‖v‖ = 1 := by
        dsimp only [v]
        rw [norm_smul, RCLike.norm_ofReal,
          abs_of_pos (inv_pos.mpr hwpos), inv_mul_cancel₀ hwpos.ne']
      refine ⟨⟨v, hv⟩, ?_⟩
      change weightedHilbertObjective a u v =
        2 * (∑ i, a i - ‖w‖)
      rw [weightedHilbertObjective_eq (𝕜 := 𝕜) a u v hu hv]
      change 2 * (∑ i, a i - RCLike.re ⟪w, v⟫_𝕜) =
        2 * (∑ i, a i - ‖w‖)
      have hinner : RCLike.re ⟪w, v⟫_𝕜 = ‖w‖ := by
        dsimp only [v]
        rw [inner_smul_right, RCLike.re_ofReal_mul,
          ← norm_sq_eq_re_inner (𝕜 := 𝕜) w]
        field_simp
      rw [hinner]

/-- Equation (7)'s minimization step in its exact abstract form.  A Mazur
sphere equivalence, attained variational representations, and a pointwise
Bregman--distance comparison imply the factors `2*m` and `2*M` between the
two gap values. -/
theorem variationalGap_two_sided_of_mazurEquiv
    {P Q : Type*} (mazur : P ≃ Q) (beta : P → ℝ) (distanceSq : Q → ℝ)
    (deltaP delta₂ m M : ℝ) (hm : 0 ≤ m)
    (hbeta : IsGlobalMinimumValue beta deltaP)
    (hdistance : IsGlobalMinimumValue distanceSq (2 * delta₂))
    (hcompare : ∀ u,
      m * distanceSq (mazur u) ≤ beta u ∧
        beta u ≤ M * distanceSq (mazur u)) :
    2 * m * delta₂ ≤ deltaP ∧ deltaP ≤ 2 * M * delta₂ := by
  have h := globalMinimumValue_two_sided_of_equiv mazur beta distanceSq
    deltaP (2 * delta₂) m M hm hbeta hdistance hcompare
  constructor
  · calc
      2 * m * delta₂ = m * (2 * delta₂) := by ring
      _ ≤ deltaP := h.1
  · calc
      deltaP ≤ M * (2 * delta₂) := h.2
      _ = 2 * M * delta₂ := by ring

section RectangularMazur

variable {E F κ : Type*} [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The rectangular Mazur equivalence followed by Hilbert--Schmidt column
coordinates identifies the Schatten-`p` power sphere with an ordinary
Hilbert unit sphere. -/
noncomputable def rectangularMazurHilbertSphereEquiv
    (e : OrthonormalBasis κ ℂ E) {p : ℝ} (hp : 0 < p) :
    schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p ≃
      unitSphere (PiLp 2 (fun _ : κ => F)) :=
  (rectangularMazurPowerSphereEquiv hp).trans
    (schattenTwoPowerSphereEquivUnitSphere e)

/-- Weighted squared Schatten-2 distance between rectangular Mazur images,
parametrized on the original Schatten-`p` power sphere. -/
noncomputable def rectangularMazurDistanceObjective
    (p : ℝ) (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (v : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) : ℝ :=
  ∑ i, a i * singularValuePowerSum 2
    (rectangularMazurMap p (u i).1 - rectangularMazurMap p v.1)

/-- Weighted barycenter of the rectangular Mazur images. -/
noncomputable def rectangularMazurBarycenter
    (p : ℝ) (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    E →ₗ[ℂ] F :=
  ∑ i, (a i : ℂ) • rectangularMazurMap p (u i).1

/-- Weighted rectangular Bregman objective, normalized by the two copies in
the Hermitian dilation. -/
noncomputable def rectangularBregmanObjective
    (p : ℝ) (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (v : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) : ℝ :=
  ∑ i, a i * (dilatedBregmanTrace p (u i).1 v.1 / 2)

/-- Weighted sum of the original Schatten-`p` unit operators. -/
noncomputable def rectangularWeightedSum
    {p : ℝ} (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    E →ₗ[ℂ] F :=
  ∑ i, (a i : ℂ) • (u i).1

/-- On power-sphere inputs, the finite Bregman objective is the total weight
minus one gradient pairing with the weighted operator sum. -/
theorem rectangularBregmanObjective_eq_sum_sub_pairing
    {p : ℝ} (hp : 0 < p) (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (v : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    rectangularBregmanObjective p a u v =
      (∑ i, a i) - dilatedGradientPairing p (rectangularWeightedSum a u) v.1 := by
  unfold rectangularBregmanObjective rectangularWeightedSum
  have hterm : ∀ i,
      dilatedBregmanTrace p (u i).1 v.1 / 2 =
        1 - dilatedGradientPairing p (u i).1 v.1 := fun i =>
    dilatedBregmanTrace_div_two_eq_one_sub_pairing hp _ _
      (u i).property v.property
  simp_rw [hterm]
  rw [dilatedGradientPairing_sum p a (fun i => (u i).1) v.1]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]

/-- The rectangular Bregman objective attains the Schatten variational gap.
This is the duality formula needed in equation (6), proved directly from
Bregman nonnegativity and positive homogeneity rather than a separate
von Neumann trace-inequality API. -/
theorem rectangularBregmanObjective_isGlobalMinimumValue
    [Nonempty ι] {p : ℝ} (hp : 1 < p) (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    IsGlobalMinimumValue (rectangularBregmanObjective p a u)
      ((∑ i, a i) - schattenPNorm p (rectangularWeightedSum a u)) := by
  let W := rectangularWeightedSum a u
  have hp0 : 0 < p := zero_lt_one.trans hp
  constructor
  · intro v
    rw [rectangularBregmanObjective_eq_sum_sub_pairing hp0 a u v]
    change (∑ i, a i) - schattenPNorm p W ≤
      (∑ i, a i) - dilatedGradientPairing p W v.1
    by_cases hW : W = 0
    · rw [hW, dilatedGradientPairing_zero, schattenPNorm_zero p hp0.ne']
    · let r := schattenPNorm p W
      have hr : 0 < r := schattenPNorm_pos p hW
      let U₀ : E →ₗ[ℂ] F := ((r⁻¹ : ℝ) : ℂ) • W
      have hnormU₀ : schattenPNorm p U₀ = 1 := by
        dsimp only [U₀]
        rw [schattenPNorm_real_smul hp0 (inv_pos.mpr hr),
          inv_mul_cancel₀ hr.ne']
      have hpowerU₀ : singularValuePowerSum p U₀ = 1 :=
        (schattenPNorm_eq_one_iff hp0 U₀).mp hnormU₀
      have hnonneg := dilatedBregmanTrace_nonneg hp U₀ v.1
      have hformula := dilatedBregmanTrace_div_two_eq_one_sub_pairing
        hp0 U₀ v.1 hpowerU₀ v.property
      have hpairU₀ : dilatedGradientPairing p U₀ v.1 ≤ 1 := by
        linarith
      have hWU₀ : W = (r : ℂ) • U₀ := by
        dsimp only [U₀]
        rw [smul_smul]
        simp [hr.ne']
      have hpairW : dilatedGradientPairing p W v.1 =
          r * dilatedGradientPairing p U₀ v.1 := by
        rw [hWU₀, dilatedGradientPairing_real_smul]
      have hle : dilatedGradientPairing p W v.1 ≤ r := by
        rw [hpairW]
        nlinarith
      exact sub_le_sub_left hle _
  · by_cases hW : W = 0
    · let i : ι := Classical.choice inferInstance
      refine ⟨u i, ?_⟩
      rw [rectangularBregmanObjective_eq_sum_sub_pairing hp0 a u (u i)]
      change (∑ j, a j) - dilatedGradientPairing p W (u i).1 =
        (∑ j, a j) - schattenPNorm p W
      rw [hW, dilatedGradientPairing_zero, schattenPNorm_zero p hp0.ne']
    · let r := schattenPNorm p W
      have hr : 0 < r := schattenPNorm_pos p hW
      let U₀ : E →ₗ[ℂ] F := ((r⁻¹ : ℝ) : ℂ) • W
      have hnormU₀ : schattenPNorm p U₀ = 1 := by
        dsimp only [U₀]
        rw [schattenPNorm_real_smul hp0 (inv_pos.mpr hr),
          inv_mul_cancel₀ hr.ne']
      have hpowerU₀ : singularValuePowerSum p U₀ = 1 :=
        (schattenPNorm_eq_one_iff hp0 U₀).mp hnormU₀
      let U : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p :=
        ⟨U₀, hpowerU₀⟩
      have hWU₀ : W = (r : ℂ) • U₀ := by
        dsimp only [U₀]
        rw [smul_smul]
        simp [hr.ne']
      have hpairSelf : dilatedGradientPairing p U₀ U₀ = 1 := by
        have hformula := dilatedBregmanTrace_div_two_eq_one_sub_pairing
          hp0 U₀ U₀ hpowerU₀ hpowerU₀
        rw [dilatedBregmanTrace_self] at hformula
        linarith
      refine ⟨U, ?_⟩
      rw [rectangularBregmanObjective_eq_sum_sub_pairing hp0 a u U]
      change (∑ i, a i) - dilatedGradientPairing p W U₀ =
        (∑ i, a i) - schattenPNorm p W
      have hpairW : dilatedGradientPairing p W U₀ =
          r * dilatedGradientPairing p U₀ U₀ := by
        rw [hWU₀, dilatedGradientPairing_real_smul]
      rw [hpairW, hpairSelf, mul_one]

/-- A two-sided comparison for each dilated Bregman divergence gives the
same comparison between the normalized finite-family Bregman objective and
the rectangular Mazur squared-distance objective. -/
theorem rectangularBregmanObjective_two_sided
    (p m M : ℝ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (v : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    m * rectangularMazurDistanceObjective p a u v ≤
        rectangularBregmanObjective p a u v ∧
      rectangularBregmanObjective p a u v ≤
        M * rectangularMazurDistanceObjective p a u v := by
  have hterm : ∀ i,
      m * singularValuePowerSum 2
          (rectangularMazurMap p (u i).1 - rectangularMazurMap p v.1) ≤
          dilatedBregmanTrace p (u i).1 v.1 / 2 ∧
        dilatedBregmanTrace p (u i).1 v.1 / 2 ≤
          M * singularValuePowerSum 2
            (rectangularMazurMap p (u i).1 - rectangularMazurMap p v.1) := by
    intro i
    have h := hbound (u i).1 v.1
    rw [dilatedMazurDistanceSq_eq_two_mul_singularValuePowerSum'] at h
    constructor <;> linarith
  constructor
  · unfold rectangularMazurDistanceObjective rectangularBregmanObjective
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      m * (a i * singularValuePowerSum 2
          (rectangularMazurMap p (u i).1 - rectangularMazurMap p v.1)) =
          a i * (m * singularValuePowerSum 2
            (rectangularMazurMap p (u i).1 - rectangularMazurMap p v.1)) := by ring
      _ ≤ a i * (dilatedBregmanTrace p (u i).1 v.1 / 2) :=
        mul_le_mul_of_nonneg_left (hterm i).1 (ha i)
  · unfold rectangularMazurDistanceObjective rectangularBregmanObjective
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      a i * (dilatedBregmanTrace p (u i).1 v.1 / 2) ≤
          a i * (M * singularValuePowerSum 2
            (rectangularMazurMap p (u i).1 - rectangularMazurMap p v.1)) :=
        mul_le_mul_of_nonneg_left (hterm i).2 (ha i)
      _ = M * (a i * singularValuePowerSum 2
          (rectangularMazurMap p (u i).1 - rectangularMazurMap p v.1)) := by ring

/-- The uniform spectral Bregman--Mazur constants compare the two actual
rectangular finite-family objectives in every matrix dimension. -/
theorem exists_uniform_rectangularBregmanObjective_two_sided
    {p : ℝ} (hp : 1 < p) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ {G K : Type*}
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
        (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := G) (F := K) p)
        (v : schattenPowerSphere (𝕜 := ℂ) (E := G) (F := K) p),
        m * rectangularMazurDistanceObjective p a u v ≤
            rectangularBregmanObjective p a u v ∧
          rectangularBregmanObjective p a u v ≤
            M * rectangularMazurDistanceObjective p a u v := by
  obtain ⟨m, M, hm, hmM, hbound⟩ :=
    exists_uniform_dilatedBregmanTrace_two_sided hp
  refine ⟨m, M, hm, hmM, ?_⟩
  intro G K _ _ _ _ _ _ u v
  exact rectangularBregmanObjective_two_sided p m M a ha u v
    (fun S T => hbound S T)

/-- The rectangular Mazur distance objective is precisely the weighted
Hilbert squared-distance objective in column coordinates. -/
theorem rectangularMazurDistanceObjective_eq_weightedHilbertObjective
    (e : OrthonormalBasis κ ℂ E) {p : ℝ} (hp : 0 < p)
    (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (v : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    rectangularMazurDistanceObjective p a u v =
      weightedHilbertObjective a
        (fun i => (rectangularMazurHilbertSphereEquiv e hp (u i)).1)
        (rectangularMazurHilbertSphereEquiv e hp v).1 := by
  unfold rectangularMazurDistanceObjective weightedHilbertObjective
    rectangularMazurHilbertSphereEquiv
  apply Fintype.sum_congr
  intro i
  congr 1
  rw [singularValuePowerSum_two_eq_norm_hilbertSchmidtCoordinates_sq e]
  rfl

/-- Hilbert coordinates carry the weighted Mazur-image barycenter to the
weighted sum of the corresponding unit vectors. -/
theorem weightedHilbertSum_rectangularMazur_eq
    (e : OrthonormalBasis κ ℂ E) {p : ℝ} (hp : 0 < p)
    (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    weightedHilbertSum (𝕜 := ℂ) a
        (fun i => (rectangularMazurHilbertSphereEquiv e hp (u i)).1) =
      hilbertSchmidtCoordinates e (rectangularMazurBarycenter p a u) := by
  unfold weightedHilbertSum rectangularMazurHilbertSphereEquiv
    rectangularMazurBarycenter
  change (∑ i, (a i : ℂ) • hilbertSchmidtCoordinates e
    (rectangularMazurMap p (u i).1)) =
    hilbertSchmidtCoordinates e
      (∑ i, (a i : ℂ) • rectangularMazurMap p (u i).1)
  exact (map_sum (hilbertSchmidtLinearEquiv e)
    (fun i => (a i : ℂ) • rectangularMazurMap p (u i).1) Finset.univ).symm

/-- Exact Hilbert-side variational representation on the actual rectangular
Schatten-`p` sphere.  In particular, the minimizing variable is genuinely a
rectangular operator; no enlargement to an ambient coordinate space occurs. -/
theorem rectangularMazurDistanceObjective_isGlobalMinimumValue
    (e : OrthonormalBasis κ ℂ E) [Nonempty ι]
    {p : ℝ} (hp : 0 < p) (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    IsGlobalMinimumValue (rectangularMazurDistanceObjective p a u)
      (2 * (∑ i, a i - schattenPNorm 2
        (rectangularMazurBarycenter p a u))) := by
  let mazur : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p ≃
      unitSphere (PiLp 2 (fun _ : κ => F)) :=
    rectangularMazurHilbertSphereEquiv (F := F) e hp
  have hu : ∀ i, ‖(mazur (u i)).1‖ = 1 :=
    fun i => (mazur (u i)).property
  have h := weightedHilbertObjective_isGlobalMinimumValue (𝕜 := ℂ)
    a (fun i => (mazur (u i)).1) hu
  have hc := (isGlobalMinimumValue_comp_equiv mazur
    (fun v : unitSphere (PiLp 2 (fun _ : κ => F)) =>
      weightedHilbertObjective a (fun i => (mazur (u i)).1) v.1)
    (2 * (∑ i, a i -
      ‖weightedHilbertSum (𝕜 := ℂ) a (fun i => (mazur (u i)).1)‖))).mpr h
  change IsGlobalMinimumValue
    (fun v => weightedHilbertObjective a
      (fun i => (mazur (u i)).1) (mazur v).1)
    (2 * (∑ i, a i -
      ‖weightedHilbertSum (𝕜 := ℂ) a (fun i => (mazur (u i)).1)‖)) at hc
  rw [show (fun v => weightedHilbertObjective a
      (fun i => (mazur (u i)).1) (mazur v).1) =
        rectangularMazurDistanceObjective p a u by
      funext v
      exact (rectangularMazurDistanceObjective_eq_weightedHilbertObjective
        e hp a u v).symm] at hc
  rw [show weightedHilbertSum (𝕜 := ℂ) a
      (fun i => (mazur (u i)).1) =
        hilbertSchmidtCoordinates e (rectangularMazurBarycenter p a u) from
      weightedHilbertSum_rectangularMazur_eq e hp a u,
    ← schattenPNorm_two_eq_norm_hilbertSchmidtCoordinates e] at hc
  exact hc

/-- Once Schatten duality supplies the Bregman variational representation,
the already-proved spectral comparison and Hilbert minimum give equation (7)
for the actual rectangular objectives.  Thus `hbeta` is the sole remaining
analytic input at this interface. -/
theorem rectangularVariationalGap_two_sided_of_bregmanRepresentation
    (e : OrthonormalBasis κ ℂ E) [Nonempty ι]
    {p m M : ℝ} (hp : 0 < p) (hm : 0 ≤ m)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (deltaP : ℝ)
    (hbeta : IsGlobalMinimumValue
      (rectangularBregmanObjective p a u) deltaP)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    2 * m * (∑ i, a i - schattenPNorm 2
        (rectangularMazurBarycenter p a u)) ≤ deltaP ∧
      deltaP ≤ 2 * M * (∑ i, a i - schattenPNorm 2
        (rectangularMazurBarycenter p a u)) := by
  apply variationalGap_two_sided_of_mazurEquiv
    (Equiv.refl (schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p))
    (rectangularBregmanObjective p a u)
    (rectangularMazurDistanceObjective p a u)
    deltaP
    (∑ i, a i - schattenPNorm 2 (rectangularMazurBarycenter p a u))
    m M hm hbeta
    (rectangularMazurDistanceObjective_isGlobalMinimumValue e hp a u)
  intro v
  simpa using rectangularBregmanObjective_two_sided p m M a ha u v hbound

/-- Equation (7) for a finite family of rectangular Schatten-`p` unit
operators.  Both variational representations, the Mazur sphere equivalence,
and the spectral comparison have now been instantiated. -/
theorem rectangularVariationalGap_two_sided
    (e : OrthonormalBasis κ ℂ E) [Nonempty ι]
    {p m M : ℝ} (hp : 1 < p) (hm : 0 ≤ m)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    2 * m * (∑ i, a i - schattenPNorm 2
        (rectangularMazurBarycenter p a u)) ≤
        (∑ i, a i) - schattenPNorm p (rectangularWeightedSum a u) ∧
      (∑ i, a i) - schattenPNorm p (rectangularWeightedSum a u) ≤
        2 * M * (∑ i, a i - schattenPNorm 2
          (rectangularMazurBarycenter p a u)) := by
  exact rectangularVariationalGap_two_sided_of_bregmanRepresentation
    e (zero_lt_one.trans hp) hm a ha u
    ((∑ i, a i) - schattenPNorm p (rectangularWeightedSum a u))
    (rectangularBregmanObjective_isGlobalMinimumValue (E := E) (F := F) hp a u) hbound

/-- A single positive finite pair of constants gives equation (7) for every
finite pair of rectangular complex Hilbert spaces. -/
theorem exists_uniform_rectangularVariationalGap_two_sided
    [Nonempty ι] {p : ℝ} (hp : 1 < p)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ {G K : Type*}
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
        (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := G) (F := K) p),
        2 * m * (∑ i, a i - schattenPNorm 2
            (rectangularMazurBarycenter p a u)) ≤
            (∑ i, a i) - schattenPNorm p (rectangularWeightedSum a u) ∧
          (∑ i, a i) - schattenPNorm p (rectangularWeightedSum a u) ≤
            2 * M * (∑ i, a i - schattenPNorm 2
              (rectangularMazurBarycenter p a u)) := by
  obtain ⟨m, M, hm, hmM, hbound⟩ :=
    exists_uniform_dilatedBregmanTrace_two_sided hp
  refine ⟨m, M, hm, hmM, ?_⟩
  intro G K _ _ _ _ _ _ u
  exact rectangularVariationalGap_two_sided (E := G) (F := K)
    (stdOrthonormalBasis ℂ G) hp hm.le a ha u (fun S T => hbound S T)

end RectangularMazur

end HlawkaSchatten
