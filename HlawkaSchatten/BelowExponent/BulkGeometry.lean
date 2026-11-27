/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

module

public import HlawkaSchatten.BelowExponent.Center
public import HlawkaSchatten.BelowExponent.Coverage
public import HlawkaSchatten.BelowExponent.Interpolation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.FinCases

/-! The written bulk parameterization and its eight-corner interpolation. -/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.mathlibStandardSet false

@[expose] public section

namespace HlawkaSchatten.BelowExponent

noncomputable section

/-- Barycentric weights `1-u`, `u(1-v)`, and `uv` on the three ordered
vertices of the facet with last coordinate zero. -/
def bulkBase (u v : ℝ) : Profile :=
  ![(1 - u) + u * (1 - v) / 2 + u * v / 3, u * (1 - v) / 2 + u * v / 3,
    u * v / 3, 0]

/-- Move radially from the centre to the ordered facet. -/
def bulkProfile (r u v : ℝ) : Profile :=
  profileLerp r centerProfile (bulkBase u v)

abbrev bulkRadius (t : Profile) : ℝ := 1 - 4 * t 3

theorem isSimplex_bulkBase {u v : ℝ} (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    IsSimplex (bulkBase u v) := by
  have hu₀ := hu.1
  have hv₀ := hv.1
  have hu₁ := sub_nonneg.mpr hu.2
  have hv₁ := sub_nonneg.mpr hv.2
  constructor
  · intro s
    fin_cases s <;> simp [bulkBase, Matrix.cons_val_two, Matrix.cons_val_three] <;> positivity
  · simp [Fin.sum_univ_four, bulkBase, Matrix.cons_val_two, Matrix.cons_val_three]
    ring

theorem isSimplex_bulkProfile {r u v : ℝ} (hr : r ∈ Set.Icc 0 1)
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) : IsSimplex (bulkProfile r u v) := by
  have hB := isSimplex_bulkBase hu hv
  have hCenter : ∑ s, centerProfile s = 1 := by norm_num [centerProfile]
  constructor
  · intro s
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hr.2) (by norm_num [centerProfile]))
      (mul_nonneg hr.1 (hB.1 s))
  · simp only [bulkProfile, profileLerp, Finset.sum_add_distrib, ← Finset.mul_sum,
      hCenter, hB.2, mul_one, sub_add_cancel]

theorem OrderedInterior.bulkRadius_nonneg {t : Profile} (ht : OrderedInterior t) :
    0 ≤ bulkRadius t := by
  change 0 ≤ 1 - 4 * t 3
  linarith only [ht.sum_four, ht.first_ge, ht.second_ge, ht.third_ge]

theorem bulkRadius_le_of_last_ge {t : Profile} (hmin : 1 / 500 ≤ t 3) :
    bulkRadius t ≤ 124 / 125 := by
  change 1 - 4 * t 3 ≤ 124 / 125
  linarith

/-- The written parametrization is surjective onto the ordered interior,
with the radius determined by the last coordinate. -/
theorem OrderedInterior.exists_bulkProfile {t : Profile} (ht : OrderedInterior t) :
    ∃ u ∈ Set.Icc (0 : ℝ) 1, ∃ v ∈ Set.Icc (0 : ℝ) 1, t = bulkProfile (bulkRadius t) u v := by
  let r := bulkRadius t
  have hs := ht.sum_four
  have hr₀ : 0 ≤ r := ht.bulkRadius_nonneg
  by_cases hr : r = 0
  · have h3 : t 3 = 1 / 4 := by dsimp [r, bulkRadius] at hr; linarith
    have h0 : t 0 = 1 / 4 := by linarith only [h3, hs, ht.first_ge, ht.second_ge, ht.third_ge]
    have h1 : t 1 = 1 / 4 := by linarith only [h3, hs, ht.first_ge, ht.second_ge, ht.third_ge]
    have h2 : t 2 = 1 / 4 := by linarith only [h3, hs, ht.first_ge, ht.second_ge, ht.third_ge]
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, 0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    change t = bulkProfile r 0 0
    rw [hr]
    funext s
    simp only [bulkProfile, profileLerp, centerProfile, sub_zero, zero_mul, one_mul, add_zero]
    fin_cases s
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · have hrp : 0 < r := lt_of_le_of_ne hr₀ (Ne.symm hr)
    let b := (2 * (t 1 - t 2)) / r
    let c := (3 * (t 2 - t 3)) / r
    let u := b + c
    let v := if u = 0 then 0 else c / u
    have hb₀ : 0 ≤ b := div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr ht.second_ge)) hr₀
    have hc₀ : 0 ≤ c := div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr ht.third_ge)) hr₀
    have hu₀ : 0 ≤ u := add_nonneg hb₀ hc₀
    have hu₁ : u ≤ 1 := by
      dsimp only [u, b, c]
      rw [← add_div]
      apply (div_le_one₀ hrp).mpr
      dsimp [r, bulkRadius]
      linarith only [hs, ht.first_ge]
    have hv : v ∈ Set.Icc (0 : ℝ) 1 := by
      by_cases hu : u = 0
      · simp [v, hu]
      · have hup : 0 < u := lt_of_le_of_ne hu₀ (Ne.symm hu)
        have hcu : c ≤ u := le_add_of_nonneg_left hb₀
        exact ⟨by simpa [v, hu] using div_nonneg hc₀ hup.le,
          by simpa [v, hu] using (div_le_one₀ hup).mpr hcu⟩
    have huv : u * v = c := by
      by_cases hu : u = 0
      · have hc : c = 0 := by dsimp [u] at hu; linarith only [hu, hb₀, hc₀]
        simp [hu, hc]
      · rw [show v = c / u by simp [v, hu], mul_div_cancel₀ _ hu]
    have huNegv : u * (1 - v) = b := by
      rw [mul_sub, mul_one, huv]
      dsimp [u]
      ring
    have hb : r * b = 2 * (t 1 - t 2) := mul_div_cancel₀ _ hr
    have hc : r * c = 3 * (t 2 - t 3) := mul_div_cancel₀ _ hr
    have hRad : r = 1 - 4 * t 3 := rfl
    refine ⟨u, ⟨hu₀, hu₁⟩, v, hv, ?_⟩
    change t = bulkProfile r u v
    funext s
    fin_cases s
    · change t 0 = (1 - r) * (1 / 4) + r * ((1 - u) + u * (1 - v) / 2 + u * v / 3)
      rw [huNegv, huv]
      dsimp only [u]
      nlinarith only [hb, hc, hRad, hs]
    · change t 1 = (1 - r) * (1 / 4) + r * (u * (1 - v) / 2 + u * v / 3)
      rw [huNegv, huv]
      nlinarith only [hb, hc, hRad]
    · change t 2 = (1 - r) * (1 / 4) + r * (u * v / 3)
      rw [huv]
      nlinarith only [hc, hRad]
    · change t 3 = (1 - r) * (1 / 4) + r * 0
      linarith only [hRad]

/-- The ordered bulk region is covered by the closed parameter box for the
written bulk subdivision. -/
theorem OrderedInterior.exists_bulkProfile_box {t : Profile} (ht : OrderedInterior t)
    (hmin : 1 / 500 ≤ t 3) :
    ∃ r ∈ Set.Icc (0 : ℝ) (127 / 128), ∃ u ∈ Set.Icc (0 : ℝ) 1,
      ∃ v ∈ Set.Icc (0 : ℝ) 1, t = bulkProfile r u v := by
  obtain ⟨u, hu, v, hv, heq⟩ := ht.exists_bulkProfile
  exact ⟨bulkRadius t, ⟨ht.bulkRadius_nonneg,
    (bulkRadius_le_of_last_ge hmin).trans (by norm_num)⟩, u, hu, v, hv, heq⟩

abbrev BulkBoxCorner := Bool × Bool × Bool

def chooseCorner {α : Type*} (b : Bool) (lo hi : α) : α := if b then hi else lo

def boxFactor (w : ℝ) (b : Bool) : ℝ := if b then w else 1 - w

def bulkBoxCorner (lo hi : Fin 3 → ℝ) (b : BulkBoxCorner) : Profile :=
  bulkProfile (chooseCorner b.1 (lo 0) (hi 0))
    (chooseCorner b.2.1 (lo 1) (hi 1)) (chooseCorner b.2.2 (lo 2) (hi 2))

def bulkBoxWeight (w : Fin 3 → ℝ) (b : BulkBoxCorner) : ℝ :=
  boxFactor (w 0) b.1 * boxFactor (w 1) b.2.1 * boxFactor (w 2) b.2.2

def interpolate (w a b : ℝ) : ℝ := (1 - w) * a + w * b

/-- The image of the parameter point with each interpolation coordinate `w i`. -/
def bulkBoxProfile (lo hi w : Fin 3 → ℝ) : Profile :=
  bulkProfile (interpolate (w 0) (lo 0) (hi 0))
    (interpolate (w 1) (lo 1) (hi 1)) (interpolate (w 2) (lo 2) (hi 2))

theorem bulkBoxWeight_nonneg {w : Fin 3 → ℝ} (hw : ∀ i, w i ∈ Set.Icc 0 1)
    (b : BulkBoxCorner) : 0 ≤ bulkBoxWeight w b := by
  have h (i : Fin 3) (flag : Bool) : 0 ≤ boxFactor (w i) flag := by
    cases flag
    · exact sub_nonneg.mpr (hw i).2
    · exact (hw i).1
  exact mul_nonneg (mul_nonneg (h 0 _) (h 1 _)) (h 2 _)

theorem sum_bulkBoxWeight (w : Fin 3 → ℝ) : ∑ b, bulkBoxWeight w b = 1 := by
  simp [Fintype.sum_prod_type, bulkBoxWeight, boxFactor]
  ring

/-- The bulk parameterization is affine in each parameter separately. -/
theorem bulkBoxProfile_eq_barycenter (lo hi w : Fin 3 → ℝ) :
    bulkBoxProfile lo hi w = ∑ b, bulkBoxWeight w b • bulkBoxCorner lo hi b := by
  funext s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_bool]
  fin_cases s <;>
    simp [bulkBoxProfile, interpolate, bulkBoxWeight, boxFactor, bulkBoxCorner, chooseCorner,
      bulkProfile, profileLerp, centerProfile, bulkBase, Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

/-- Eight certificates with common output weights certify every point in a
parameter box. The input weights may vary between corners. -/
theorem rowAt_bulkBox {q : ℝ} {lo hi w : Fin 3 → ℝ} {π : Profile} {γ : BulkBoxCorner → Row}
    (hq : 1 ≤ q) (hw : ∀ i, w i ∈ Set.Icc 0 1) (hπ : IsSimplex π)
    (hγ : ∀ b j, 0 ≤ γ b j) (hBudget : ∀ b, ∑ j, γ b j ≤ 1)
    (hRows : ∀ b x, WeightedRow q (bulkBoxCorner lo hi b) π (γ b) x) :
    RowAt q (bulkBoxProfile lo hi w) := by
  rw [bulkBoxProfile_eq_barycenter]
  exact rowAt_barycenter hq (fun b _ => bulkBoxWeight_nonneg hw b) (sum_bulkBoxWeight w) hπ
    (fun b _ => hγ b) (fun b _ => hBudget b) (fun b _ => hRows b)

/-- Between the outer knots of any finite list, some consecutive pair
brackets the given point. -/
theorem exists_adjacent_knots (n : ℕ) {f : Fin (n + 2) → ℝ} {x : ℝ}
    (h₀ : f 0 ≤ x) (h₁ : x ≤ f (Fin.last (n + 1))) :
    ∃ i : Fin (n + 1), f i.castSucc ≤ x ∧ x ≤ f i.succ := by
  induction n with
  | zero => exact ⟨0, h₀, h₁⟩
  | succ n ih =>
    by_cases hm : x ≤ f (Fin.last (n + 1)).castSucc
    · let g : Fin (n + 2) → ℝ := fun j => f j.castSucc
      obtain ⟨i, hlow, hhigh⟩ := ih (f := g) h₀ hm
      exact ⟨i.castSucc, hlow, hhigh⟩
    · exact ⟨Fin.last (n + 1), (lt_of_not_ge hm).le, h₁⟩

theorem exists_interval_lerp {a b x : ℝ} (h₀ : a ≤ x) (h₁ : x ≤ b) :
    ∃ w ∈ Set.Icc (0 : ℝ) 1, x = (1 - w) * a + w * b := by
  by_cases hab : a = b
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    simpa using le_antisymm (hab.symm ▸ h₁) h₀
  · have hd := sub_pos.mpr (lt_of_le_of_ne (h₀.trans h₁) hab)
    let w := (x - a) / (b - a)
    refine ⟨w, ⟨div_nonneg (sub_nonneg.mpr h₀) hd.le,
      (div_le_one₀ hd).mpr (sub_le_sub_right h₁ a)⟩, ?_⟩
    calc
      x = a + w * (b - a) := by
        dsimp only [w]
        rw [div_mul_cancel₀ _ hd.ne']
        ring
      _ = _ := by ring

def radialKnotNum : Fin 15 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 48, 64, 80, 96, 112, 120, 124, 126, 127]

def facetKnotNum : Fin 7 → ℕ := ![0, 1, 4, 8, 16, 24, 32]

def radialKnot (i : Fin 15) : ℝ := (radialKnotNum i : ℝ) / 128

def facetKnot (i : Fin 7) : ℝ := (facetKnotNum i : ℝ) / 32

/-- The written grid has fourteen radial slabs and six intervals in each
facet coordinate. The index order is radial, then the two facet coordinates. -/
abbrev BulkGridCell := Fin 14 × Fin 6 × Fin 6

def bulkGridLower (cell : BulkGridCell) : Fin 3 → ℝ :=
  ![radialKnot cell.1.castSucc, facetKnot cell.2.1.castSucc, facetKnot cell.2.2.castSucc]

def bulkGridUpper (cell : BulkGridCell) : Fin 3 → ℝ :=
  ![radialKnot cell.1.succ, facetKnot cell.2.1.succ, facetKnot cell.2.2.succ]

theorem exists_bulkGridCell {r u v : ℝ} (hr : r ∈ Set.Icc (1 / 128) (127 / 128))
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    ∃ (cell : BulkGridCell) (w : Fin 3 → ℝ), (∀ j, w j ∈ Set.Icc 0 1) ∧
      bulkProfile r u v = bulkBoxProfile (bulkGridLower cell) (bulkGridUpper cell) w := by
  have huLo : facetKnot 0 ≤ u := by simpa [facetKnot, facetKnotNum] using hu.1
  have hvLo : facetKnot 0 ≤ v := by simpa [facetKnot, facetKnotNum] using hv.1
  have huHi : u ≤ facetKnot (Fin.last 6) := by change u ≤ (32 : ℝ) / 32; norm_num; exact hu.2
  have hvHi : v ≤ facetKnot (Fin.last 6) := by change v ≤ (32 : ℝ) / 32; norm_num; exact hv.2
  have hrLo : radialKnot 0 ≤ r := by simpa [radialKnot, radialKnotNum] using hr.1
  obtain ⟨i, hr₀, hr₁⟩ := exists_adjacent_knots 13 (f := radialKnot) hrLo hr.2
  obtain ⟨j, hu₀, hu₁⟩ := exists_adjacent_knots 5 huLo huHi
  obtain ⟨k, hv₀, hv₁⟩ := exists_adjacent_knots 5 hvLo hvHi
  obtain ⟨a, ha, hra⟩ := exists_interval_lerp hr₀ hr₁
  obtain ⟨b, hb, hub⟩ := exists_interval_lerp hu₀ hu₁
  obtain ⟨c, hc, hvc⟩ := exists_interval_lerp hv₀ hv₁
  refine ⟨(i, j, k), ![a, b, c], ?_, ?_⟩
  · intro s
    fin_cases s
    · exact ha
    · exact hb
    · exact hc
  · change bulkProfile r u v =
      bulkProfile (interpolate a (radialKnot i.castSucc) (radialKnot i.succ))
        (interpolate b (facetKnot j.castSucc) (facetKnot j.succ))
        (interpolate c (facetKnot k.castSucc) (facetKnot k.succ))
    simp only [interpolate, ← hra, ← hub, ← hvc]

theorem bulkBase_dist_center_sq {u v : ℝ} (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    ∑ s, (bulkBase u v s - centerProfile s) ^ 2 ≤ 3 / 4 := by
  let b := bulkBase u v
  have hb := isSimplex_bulkBase hu hv
  have hCoord (s : Fin 4) : b s ≤ 1 := by
    calc
      _ ≤ ∑ j, b j := Finset.single_le_sum (fun j _ => hb.1 j) (Finset.mem_univ s)
      _ = _ := hb.2
  have hSq : ∑ s, b s ^ 2 ≤ 1 := calc
    _ ≤ ∑ s, b s := Finset.sum_le_sum fun s _ => by
      simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left (hCoord s) (hb.1 s)
    _ = _ := hb.2
  have hSum : b 0 + b 1 + b 2 + b 3 = 1 := by
    have h := hb.2
    rw [Fin.sum_univ_four] at h
    exact h
  calc
    _ = (∑ s, b s ^ 2) - 1 / 4 := by
      change (∑ s, (b s - centerProfile s) ^ 2) = _
      simp only [Fin.sum_univ_four, centerProfile]
      nlinarith only [hSum]
    _ ≤ _ := by linarith

/-- The inner radial interval lies strictly inside the written centre collar. -/
theorem bulkProfile_near_center {r u v : ℝ} (hr : r ∈ Set.Icc 0 (1 / 128))
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    ∑ s, (bulkProfile r u v s - centerProfile s) ^ 2 < (1 / 100 : ℝ) ^ 2 := by
  have h (s : Fin 4) : bulkProfile r u v s - centerProfile s =
      r * (bulkBase u v s - centerProfile s) := by unfold bulkProfile profileLerp; ring
  simp_rw [h, mul_pow, ← Finset.mul_sum]
  calc
    _ ≤ r ^ 2 * (3 / 4) :=
      mul_le_mul_of_nonneg_left (bulkBase_dist_center_sq hu hv) (sq_nonneg _)
    _ ≤ (1 / 128 : ℝ) ^ 2 * (3 / 4) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.1 hr.2 2) (by norm_num)
    _ < _ := by norm_num

/-- The ordered bulk is covered by the centre collar and the 504 prescribed
parameter cells, independently of the choices of certificate weights. -/
theorem OrderedInterior.bulk_grid_cover {t : Profile} (ht : OrderedInterior t)
    (hmin : 1 / 500 ≤ t 3) :
    (∑ s, (t s - centerProfile s) ^ 2) < (1 / 100 : ℝ) ^ 2 ∨
      ∃ (cell : BulkGridCell) (w : Fin 3 → ℝ), (∀ j, w j ∈ Set.Icc 0 1) ∧
        t = bulkBoxProfile (bulkGridLower cell) (bulkGridUpper cell) w := by
  obtain ⟨r, hr, u, hu, v, hv, heq⟩ := ht.exists_bulkProfile_box hmin
  rw [heq]
  by_cases h : r ≤ 1 / 128
  · exact Or.inl (bulkProfile_near_center ⟨hr.1, h⟩ hu hv)
  · exact Or.inr (exists_bulkGridCell ⟨(lt_of_not_ge h).le, hr.2⟩ hu hv)

def knotAt {n : ℕ} (f : Fin (n + 2) → ℕ) (i : Fin (n + 1)) (b : Bool) : ℕ :=
  chooseCorner b (f i.castSucc) (f i.succ)

/-- The common profile denominator of the written bulk arithmetic. -/
def bulkGridProfileDen : ℕ := 3 * 2 ^ 24

def bulkProfileNums (r u v : ℕ) : Fin 4 → ℕ :=
  let base := 98304 * (128 - r)
  let a := 12288 * r * (32 - u)
  let b := 192 * r * u * (32 - v)
  let c := 128 * r * u * v
  ![base + a + b + c, base + b + c, base + c, base]

/-- Integer representation of a mapped corner in the prescribed parameter grid. -/
def bulkGridCornerNums (cell : BulkGridCell) (b : BulkBoxCorner) : Fin 4 → ℕ :=
  bulkProfileNums (knotAt radialKnotNum cell.1 b.1)
    (knotAt facetKnotNum cell.2.1 b.2.1) (knotAt facetKnotNum cell.2.2 b.2.2)

private theorem bulkProfile_eq_num {r u v : ℕ} (hr : r ≤ 128) (hu : u ≤ 32) (hv : v ≤ 32) :
    bulkProfile ((r : ℝ) / 128) ((u : ℝ) / 32) ((v : ℝ) / 32) =
      fun s => (bulkProfileNums r u v s : ℝ) / bulkGridProfileDen := by
  funext s
  fin_cases s <;>
    simp [bulkProfile, profileLerp, centerProfile, bulkBase, bulkProfileNums, bulkGridProfileDen,
      Matrix.cons_val_two, Matrix.cons_val_three, Nat.cast_sub hr, Nat.cast_sub hu, Nat.cast_sub hv] <;> ring

private theorem radialNum_le : ∀ i : Fin 15, radialKnotNum i ≤ 128 := by decide

private theorem facetNum_le : ∀ i : Fin 7, facetKnotNum i ≤ 32 := by decide

private theorem knotAt_le {n a : ℕ} {f : Fin (n + 2) → ℕ} (h : ∀ i, f i ≤ a)
    (i : Fin (n + 1)) (b : Bool) : knotAt f i b ≤ a := by
  cases b
  · exact h i.castSucc
  · exact h i.succ

private theorem chooseCorner_div_cast (b : Bool) (x y : ℕ) (d : ℝ) :
    chooseCorner b ((x : ℝ) / d) ((y : ℝ) / d) = (chooseCorner b x y : ℕ) / d := by
  cases b <;> rfl

theorem bulkGridCorner_eq_div (cell : BulkGridCell) (b : BulkBoxCorner) :
    bulkBoxCorner (bulkGridLower cell) (bulkGridUpper cell) b =
      fun s => (bulkGridCornerNums cell b s : ℝ) / bulkGridProfileDen := by
  change bulkProfile (chooseCorner b.1 ((radialKnotNum cell.1.castSucc : ℝ) / 128)
      ((radialKnotNum cell.1.succ : ℝ) / 128))
    (chooseCorner b.2.1 ((facetKnotNum cell.2.1.castSucc : ℝ) / 32) ((facetKnotNum cell.2.1.succ : ℝ) / 32))
    (chooseCorner b.2.2 ((facetKnotNum cell.2.2.castSucc : ℝ) / 32) ((facetKnotNum cell.2.2.succ : ℝ) / 32)) = _
  simp only [chooseCorner_div_cast]
  exact bulkProfile_eq_num (knotAt_le radialNum_le _ _) (knotAt_le facetNum_le _ _) (knotAt_le facetNum_le _ _)

def bulkCenterCornerOK (cell : BulkGridCell) (b : BulkBoxCorner) : Prop :=
  (10000 : ℤ) * (∑ s, (4 * (bulkGridCornerNums cell b s : ℤ) - bulkGridProfileDen) ^ 2) ≤
    16 * (bulkGridProfileDen : ℤ) ^ 2

instance (cell : BulkGridCell) (b : BulkBoxCorner) : Decidable (bulkCenterCornerOK cell b) := by
  unfold bulkCenterCornerOK
  infer_instance

/-- Every mapped corner passes the written integer distance test. -/
def bulkCenterCellOK (cell : BulkGridCell) : Prop := ∀ b, bulkCenterCornerOK cell b

instance (cell : BulkGridCell) : Decidable (bulkCenterCellOK cell) := by
  unfold bulkCenterCellOK
  infer_instance

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem card_bulkCenterCells : (Finset.univ.filter bulkCenterCellOK).card = 12 := by decide +kernel

private theorem bulkCenterCorner_sound {cell : BulkGridCell} {b : BulkBoxCorner}
    (h : bulkCenterCornerOK cell b) :
    ∑ s, (bulkBoxCorner (bulkGridLower cell) (bulkGridUpper cell) b s - centerProfile s) ^ 2 ≤
      (1 / 100 : ℝ) ^ 2 := by
  rw [bulkGridCorner_eq_div]
  have hReal : (10000 : ℝ) * (∑ s, (4 * (bulkGridCornerNums cell b s : ℝ) - bulkGridProfileDen) ^ 2) ≤
      16 * (bulkGridProfileDen : ℝ) ^ 2 := by
    exact_mod_cast h
  have hScale (s : Fin 4) :
      4 * (bulkGridCornerNums cell b s : ℝ) - bulkGridProfileDen =
        (4 * (bulkGridProfileDen : ℝ)) *
          ((bulkGridCornerNums cell b s : ℝ) / bulkGridProfileDen - centerProfile s) := by
    norm_num [centerProfile, bulkGridProfileDen]
    ring
  simp_rw [hScale, mul_pow, ← Finset.mul_sum] at hReal
  norm_num [bulkGridProfileDen] at hReal ⊢
  linarith only [hReal]

/-- Convexity of the squared distance extends a corner bound throughout a
profile box. -/
theorem bulkBoxProfile_dist_center_sq_le {lo hi w : Fin 3 → ℝ} {d : ℝ}
    (hw : ∀ i, w i ∈ Set.Icc 0 1)
    (hCorner : ∀ b, ∑ s, (bulkBoxCorner lo hi b s - centerProfile s) ^ 2 ≤ d) :
    ∑ s, (bulkBoxProfile lo hi w s - centerProfile s) ^ 2 ≤ d := by
  have hW := fun b : BulkBoxCorner => bulkBoxWeight_nonneg hw b
  have hSum := sum_bulkBoxWeight w
  have hDiff (s : Fin 4) : bulkBoxProfile lo hi w s - centerProfile s =
      ∑ b, bulkBoxWeight w b * (bulkBoxCorner lo hi b s - centerProfile s) := by
    have hAt := congrFun (bulkBoxProfile_eq_barycenter lo hi w) s
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hAt
    rw [hAt]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hSum, one_mul]
  have hSq : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ (2 : ℕ)) :=
    (by decide : Even (2 : ℕ)).convexOn_pow
  calc
    _ ≤ ∑ s, ∑ b, bulkBoxWeight w b * (bulkBoxCorner lo hi b s - centerProfile s) ^ 2 := by
      refine Finset.sum_le_sum fun s _ => ?_
      rw [hDiff]
      simpa only [smul_eq_mul] using hSq.map_sum_le (t := Finset.univ)
        (w := bulkBoxWeight w) (p := fun b => bulkBoxCorner lo hi b s - centerProfile s)
        (fun b _ => hW b) hSum (fun _ _ => Set.mem_univ _)
    _ = ∑ b, bulkBoxWeight w b * (∑ s, (bulkBoxCorner lo hi b s - centerProfile s) ^ 2) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ b, bulkBoxWeight w b * d :=
      Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hCorner b) (hW b)
    _ = _ := by rw [← Finset.sum_mul, hSum, one_mul]

theorem bulkCenterCell_sound {cell : BulkGridCell} (h : bulkCenterCellOK cell)
    {w : Fin 3 → ℝ} (hw : ∀ i, w i ∈ Set.Icc 0 1) :
    ∑ s, (bulkBoxProfile (bulkGridLower cell) (bulkGridUpper cell) w s - centerProfile s) ^ 2 ≤
      (1 / 100 : ℝ) ^ 2 :=
  bulkBoxProfile_dist_center_sq_le hw fun b => bulkCenterCorner_sound (h b)

/-- A certificate for the centre collar and common-output-weight certificates
at the remaining cell corners suffice for the ordered bulk region. -/
theorem rowAt_ordered_bulk_of_checks {q : ℝ} (hq : 1 ≤ q)
    (hCenter : ∀ t, OrderedInterior t →
      (∑ s, (t s - centerProfile s) ^ 2 ≤ (1 / 100 : ℝ) ^ 2) → RowAt q t)
    (hCells : ∀ cell, ¬ bulkCenterCellOK cell →
      ∃ π, IsSimplex π ∧ ∃ γ : BulkBoxCorner → Row,
        (∀ b j, 0 ≤ γ b j) ∧ (∀ b, ∑ j, γ b j ≤ 1) ∧
        ∀ b x, WeightedRow q (bulkBoxCorner (bulkGridLower cell) (bulkGridUpper cell) b) π (γ b) x)
    {t : Profile} (ht : OrderedInterior t) (hmin : 1 / 500 ≤ t 3) :
    RowAt q t := by
  rcases ht.bulk_grid_cover hmin with hNear | ⟨cell, w, hw, heq⟩
  · exact hCenter t ht hNear.le
  · by_cases hc : bulkCenterCellOK cell
    · exact hCenter t ht (heq.symm ▸ bulkCenterCell_sound hc hw)
    · obtain ⟨π, hπ, γ, hγ, hBudget, hRows⟩ := hCells cell hc
      rw [heq]
      exact rowAt_bulkBox hq hw hπ hγ hBudget hRows

end

end HlawkaSchatten.BelowExponent
